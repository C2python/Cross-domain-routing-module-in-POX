# Cross-domain-routing-module-in-POX
# Copyright 2012-2013 James McCauley
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at:
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
A shortest-path forwarding application.

This is a standalone L2 switch that learns ethernet addresses
across the entire network and picks short paths between them.

You shouldn't really write an application this way -- you should
keep more state in the controller (that is, your flow tables),
and/or you should make your topology more static.  However, this
does (mostly) work. :)

Depends on openflow.discovery
Works with openflow.spanning_tree
"""
# -*- coding: utf-8 -*-
from pox.core import core
import pox.openflow.libopenflow_01 as of
from pox.lib.packet.dhcp import dhcp
from pox.lib.revent import *
from pox.lib.recoco import Timer
from collections import defaultdict
from pox.openflow.discovery import Discovery
from pox.lib.util import dpid_to_str
import time
from pox.lib.addresses import IPAddr,EthAddr
import copy

log = core.getLogger()

# Adjacency map.  [sw1][sw2] -> port from sw1 to sw2
adjacency = defaultdict(lambda:defaultdict(lambda:None))

# Switches we know of.  [dpid] -> Switch
switches = {}

#Switches in each domain
sws1=[]   #for domain
sws2=[]   #for domain
sws3=[]   #for domain
sws4=[]
sws5=[]
sws6=[]
#border switch in each domain
sws1_b=[]
sws2_b=[]
sws3_b=[]
sws4_b=[]
sws5_b=[]
sws6_b=[]
sws_b=[]   #for all the border switches

FLOW_IDLE_TIMEOUT = 3000
FLOW_HARD_TIMEOUT = 3000
FLOW_IDLE_TIMEOUT_FOR = 5000
FLOW_HARD_TIMEOUT_FOR = 5000
PREROUTE_START_TIME=25
CALC_PATHS_TIME=20
PATH_SETUP_TIME=4
_Del_Storm_Time_=5

# ethaddr -> (switch, port)
mac_map = {}

#buffer pakckets :dpid->{packet...}
buffer_packets={}
#buffer packets that have sloved:dpid->match
packets_record={}

# [sw1][sw2] -> (distance, intermediate)
path_map = defaultdict(lambda:defaultdict(lambda:(None,None)))
path_map_one = defaultdict(lambda:defaultdict(lambda:(None,None)))

# Waiting path.  (dpid,xid)->WaitingPath
waiting_paths = {}

# Time to not flood in seconds
FLOOD_HOLDDOWN = 5

# Flow timeouts
FLOW_IDLE_TIMEOUT = 100
FLOW_HARD_TIMEOUT = 300

# How long is allowable to set up a path?
PATH_SETUP_TIME = 8


def _Timer_func():
  buffer_packets.clear()

def _calc_paths ():
  """
  Essentially Floyd-Warshall algorithm
  """

  def dump ():
    for i in sws:
      for j in sws:
        a = path_map[i][j][0]
        #a = adjacency[i][j]
        if a is None: a = "*"
        print a,
      print

  sws = switches.values()
  path_map.clear()
  for k in sws:
    for j,port in adjacency[k].iteritems():
      if port is None: continue
      path_map[k][j] = (1,None)
    path_map[k][k] = (0,None) # distance, intermediate

  #dump()

  for k in sws:
    for i in sws:
      for j in sws:
        if path_map[i][k][0] is not None:
          if path_map[k][j][0] is not None:
            # i -> k -> j exists
            ikj_dist = path_map[i][k][0]+path_map[k][j][0]
            if path_map[i][j][0] is None or ikj_dist < path_map[i][j][0]:
              # i -> k -> j is better than existing
              path_map[i][j] = (ikj_dist, k)

  #print "--------------------"
  #dump()


def _get_raw_path (src, dst):
  """
  Get a raw path (just a list of nodes to traverse)
  """
  if len(path_map) == 0: _calc_paths()
  if src is dst:
    # We're here!
    return []
  if path_map[src][dst][0] is None:
    return None
  intermediate = path_map[src][dst][1]
  if intermediate is None:
    # Directly connected
    return []
  return _get_raw_path(src, intermediate) + [intermediate] + \
         _get_raw_path(intermediate, dst)


def _check_path (p):
  """
  Make sure that a path is actually a string of nodes with connected ports

  returns True if path is valid
  """
  for a,b in zip(p[:-1],p[1:]):
    if adjacency[a[0]][b[0]] != a[2]:
      return False
    if adjacency[b[0]][a[0]] != b[1]:
      return False
  return True


def _get_path (src, dst, first_port, final_port):
  """
  Gets a cooked path -- a list of (node,in_port,out_port)
  """
  # Start with a raw path...
  if src == dst:
    path = [src]
  else:
    path = _get_raw_path(src, dst)
    if path is None: return None
    path = [src] + path + [dst]

  # Now add the ports
  r = []
  in_port = first_port
  for s1,s2 in zip(path[:-1],path[1:]):
    out_port = adjacency[s1][s2]
    r.append((s1,in_port,out_port))
    in_port = adjacency[s2][s1]
  r.append((dst,in_port,final_port))

  assert _check_path(r), "Illegal path!"

  return r
#zhen dui yi yu de lu jing ji suan
def _calc_paths_one (sws):#for one domain
  #path_map.clear()#path_map:[sw1][sw2] -> (distance, intermediate)
  def dump ():
    for i in sws:
      for j in sws:
        a = path_map_one[i][j][0]
        #a = adjacency[i][j]
        if a is None: a = "*"
        print a,
      print
  for i in sws:
    for j in sws:
      path_map_one[i][j]=(None,None)
  
  for i in sws:
    for j in sws:
      if adjacency[i][j]==None: continue#adjacency:[sw1][sw2] -> port from sw1 to sw2
      path_map_one[i][j]=(1,None)
    path_map_one[i][i]=(0,None)
    
  for k in sws:
    for i in sws:
      for j in sws:
        if path_map_one[i][k][0] is not None:
          if path_map_one[k][j][0] is not None:
            # i -> k -> j exists
            ikj_dist = path_map_one[i][k][0]+path_map_one[k][j][0]
            if path_map_one[i][j][0] is None or ikj_dist < path_map_one[i][j][0]:
              # i -> k -> j is better than existing
              path_map_one[i][j] = (ikj_dist, k)
  dump()

def _get_raw_path_one (src, dst):#src and dst are all Switch objects
  """
  Get a raw path (just a list of nodes to traverse) return a list
  #return a list,list's element is a switch object
  """
  #_calc_paths_one(sws)#invoke calc_paths
  if src is dst:
    # We're here!
    return []
  if path_map_one[src][dst][0] is None:
    return None
  intermediate = path_map_one[src][dst][1]
  if intermediate is None:
    # Directly connected
    return []
  return _get_raw_path_one(src, intermediate) + [intermediate] + \
         _get_raw_path_one(intermediate, dst)#die dai

def _get_path_one (src, dst, first_port, final_port, sws):
  """
  Gets a cooked path r -- a list of (node,in_port,out_port) element is tuple
  src,dst:are all switch objects
  """
  # Start with a raw path...
  if src == dst:
    path = [src]
  else:
    _calc_paths_one(sws)
    path = _get_raw_path_one(src, dst)#return a list,list's element is a switch object
    if path is None: return None
    path = [src] + path + [dst]

  # Now add the ports
  r = []
  in_port = first_port
  for s1,s2 in zip(path[:-1],path[1:]):
    out_port = adjacency[s1][s2]
    r.append((s1,in_port,out_port))
    in_port = adjacency[s2][s1]
  r.append((dst,in_port,final_port))

  assert _check_path(r), "Illegal path!"

  return r
##################################

######-----pre-routing------######
def _pre_route ():#by lhc
  log.debug("start pre_route process")
  fobj=open('/home/zhangwen/test_file/record.txt','a+')
  fobj.write('start pre_route process\n')
  clear = of.ofp_flow_mod(command=of.OFPFC_DELETE)
  for sw in switches.itervalues():
    if sw.connection is None: continue
    sw.connection.send(clear)
  #For domain one
  _calc_paths_one(sws1)
  for i in sws1_b:
    fobj.write('border %s in domain 1\n' % i.dpid)
    for j in sws1_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain1\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)    
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end one
  #For domain two
  _calc_paths_one(sws2)
  for i in sws2_b:
    fobj.write('border %s in domain 2\n' % i.dpid)
    for j in sws2_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain2\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end two
  #For domain three
  _calc_paths_one(sws3)
  for i in sws3_b:
    fobj.write('border %s in domain 3\n' % i.dpid)
    for j in sws3_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain3\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end three
  _calc_paths_one(sws4)
  for i in sws4_b:
    fobj.write('border %s in domain 4\n' % i.dpid)
    for j in sws4_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain4\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end four
  _calc_paths_one(sws5)
  for i in sws5_b:
    fobj.write('border %s in domain 5\n' % i.dpid)
    for j in sws5_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain5\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end five
  _calc_paths_one(sws6)
  for i in sws6_b:
    fobj.write('border %s in domain 6\n' % i.dpid)
    for j in sws6_b:
      if i==j: continue
      path=[i]+_get_raw_path_one(i,j)+[j]
      log.debug("%s to %s path is %s",i,j,path)
      fobj.write('%s to %s path is %s in domain6\n' % (i.dpid,j.dpid,path))
      for s1,s2 in zip(path[:-1],path[1:]):
        msg=of.ofp_flow_mod()
        match=of.ofp_match()
        match.dl_dst=EthAddr(dpid_to_str(j.dpid))
        msg.match=match
        msg.idle_timeout=FLOW_IDLE_TIMEOUT_FOR
        msg.hard_timeout=FLOW_HARD_TIMEOUT_FOR
        out_port=adjacency[s1][s2]
        msg.actions.append(of.ofp_action_output(port=out_port))
        s1.connection.send(msg)
        fobj.write("%s switch adjacency %s switch port is %i\n" % (s1,s2,out_port))
  #end six
  fobj.close()
######----end-pre_route-----######

class WaitingPath (object):
  """
  A path which is waiting for its path to be established
  """
  def __init__ (self, path, packet):
    """
    xids is a sequence of (dpid,xid)
    first_switch is the DPID where the packet came from
    packet is something that can be sent in a packet_out
    """
    self.expires_at = time.time() + PATH_SETUP_TIME
    self.path = path
    self.first_switch = path[0][0].dpid
    self.xids = set()
    self.packet = packet

    if len(waiting_paths) > 1000:
      WaitingPath.expire_waiting_paths()

  def add_xid (self, dpid, xid):
    self.xids.add((dpid,xid))
    waiting_paths[(dpid,xid)] = self

  @property
  def is_expired (self):
    return time.time() >= self.expires_at

  def notify (self, event):
    """
    Called when a barrier has been received
    """
    self.xids.discard((event.dpid,event.xid))
    if len(self.xids) == 0:
      # Done!
      if self.packet:
        log.debug("Sending delayed packet out %s"
                  % (dpid_to_str(self.first_switch),))
        msg = of.ofp_packet_out(data=self.packet,
            action=of.ofp_action_output(port=of.OFPP_TABLE))
        core.openflow.sendToDPID(self.first_switch, msg)

      core.l2_multi.raiseEvent(PathInstalled(self.path))


  @staticmethod
  def expire_waiting_paths ():
    packets = set(waiting_paths.values())
    killed = 0
    for p in packets:
      if p.is_expired:
        killed += 1
        for entry in p.xids:
          waiting_paths.pop(entry, None)
    if killed:
      log.error("%i paths failed to install" % (killed,))


class PathInstalled (Event):
  """
  Fired when a path is installed
  """
  def __init__ (self, path):
    Event.__init__(self)
    self.path = path


class Switch (EventMixin):
  def __init__ (self):
    self.connection = None
    self.ports = None
    self.dpid = None
    self._listeners = None
    self._connected_at = None

  def __repr__ (self):
    return dpid_to_str(self.dpid)

  def _install (self, switch, in_port, out_port, match, buf = None):
    msg = of.ofp_flow_mod()
    msg.match = match
    msg.match.in_port = in_port
    msg.idle_timeout = FLOW_IDLE_TIMEOUT
    msg.hard_timeout = FLOW_HARD_TIMEOUT
    msg.actions.append(of.ofp_action_output(port = out_port))
    msg.buffer_id = buf
    switch.connection.send(msg)

  def _install_path (self, p, match, packet_in=None):
    #wp = WaitingPath(p, packet_in)
    for sw,in_port,out_port in p:
      ##########################################
      #self._install(sw, in_port, out_port, match)
      self._install(sw, in_port, out_port, match,packet_in.buffer_id)
      #msg = of.ofp_barrier_request()
      #sw.connection.send(msg)
     # wp.add_xid(sw.dpid,msg.xid)

  def install_path (self, dst_sw, last_port, match, event):
    """
    Attempts to install a path between this switch and some destination
    """
    p = _get_path(self, dst_sw, event.port, last_port)
    if p is None:
      log.warning("Can't get from %s to %s", match.nw_src, match.nw_dst)

      import pox.lib.packet as pkt

      if (match.dl_type == pkt.ethernet.IP_TYPE and
          event.parsed.find('ipv4')):
        # It's IP -- let's send a destination unreachable
        log.debug("Dest unreachable (%s -> %s)",
                  match.dl_src, match.dl_dst)

        from pox.lib.addresses import EthAddr
        e = pkt.ethernet()
        e.src = EthAddr(dpid_to_str(self.dpid)) #FIXME: Hmm...
        e.dst = match.dl_src
        e.type = e.IP_TYPE
        ipp = pkt.ipv4()
        ipp.protocol = ipp.ICMP_PROTOCOL
        ipp.srcip = match.nw_dst #FIXME: Ridiculous
        ipp.dstip = match.nw_src
        icmp = pkt.icmp()
        icmp.type = pkt.ICMP.TYPE_DEST_UNREACH
        icmp.code = pkt.ICMP.CODE_UNREACH_HOST
        orig_ip = event.parsed.find('ipv4')

        d = orig_ip.pack()
        d = d[:orig_ip.hl * 4 + 8]
        import struct
        d = struct.pack("!HH", 0,0) + d #FIXME: MTU
        icmp.payload = d
        ipp.payload = icmp
        e.payload = ipp
        msg = of.ofp_packet_out()
        msg.actions.append(of.ofp_action_output(port = event.port))
        msg.data = e.pack()
        self.connection.send(msg)

      return    

    log.debug("Installing path for %s -> %s %04x (%i hops)",
        match.nw_src, match.nw_dst, match.dl_type, len(p))

    # We have a path -- install it
    self._install_path(p, match, event.ofp)
    # Now reverse it and install it backwards
    # (we'll just assume that will work)
    p = [(sw,out_port,in_port) for sw,in_port,out_port in p]
    self._install_path(p, match.flip(),event.ofp)
    
  def install_path_one (self, dst_sw, last_port, match, event, sws):
    """
    dst_sw:a switch object
    Attempts to install a path between this switch and some destination
    """
    p = _get_path_one(self, dst_sw, event.port, last_port, sws)#p:is a list,the element is a tuple
    if p is None:
      log.warning("Can't get from %s to %s", match.nw_src, match.nw_dst)

      import pox.lib.packet as pkt

      if (match.dl_type == pkt.ethernet.IP_TYPE and#dl_type:ethernet frame type
          event.parsed.find('ipv4')):
        # It's IP -- let's send a destination unreachable
        log.debug("Dest unreachable (%s -> %s)",
                  match.dl_src, match.dl_dst)#ethernet address

        from pox.lib.addresses import EthAddr
        e = pkt.ethernet()
        e.src = EthAddr(dpid_to_str(self.dpid)) #FIXME: Hmm...
        e.dst = match.dl_src
        e.type = e.IP_TYPE
        ipp = pkt.ipv4()
        ipp.protocol = ipp.ICMP_PROTOCOL
        ipp.srcip = match.nw_dst #FIXME: Ridiculous
        ipp.dstip = match.nw_src
        icmp = pkt.icmp()
        icmp.type = pkt.ICMP.TYPE_DEST_UNREACH
        icmp.code = pkt.ICMP.CODE_UNREACH_HOST
        orig_ip = event.parsed.find('ipv4')#Find the specified protocol layer based on its class type or name.

        d = orig_ip.pack()
        d = d[:orig_ip.hl * 4 + 8]
        import struct
        d = struct.pack("!HH", 0,0) + d #FIXME: MTU
        icmp.payload = d
        ipp.payload = icmp
        e.payload = ipp
        msg = of.ofp_packet_out()
        msg.actions.append(of.ofp_action_output(port = event.port))
        msg.data = e.pack()
        self.connection.send(msg)

      return

    log.debug("Installing path for %s -> %s %04x (%i hops)",
        match.nw_src, match.nw_dst, match.dl_type, len(p))

    # We have a path -- install it
    self._install_path(p, match, event.ofp)

    # Now reverse it and install it backwards
    # (we'll just assume that will work)
    p = [(sw,out_port,in_port) for sw,in_port,out_port in p]
    self._install_path(p, match.flip())

  
  def _handle_PacketIn (self, event):
    fobj_in=open('/home/zhangwen/test_file/packet_in.txt','a+')
    def flood ():
      """ Floods the packet """
      if self.is_holding_down:
        log.warning("Not flooding -- holddown active")
      msg = of.ofp_packet_out()
      # OFPP_FLOOD is optional; some switches may need OFPP_ALL
      msg.actions.append(of.ofp_action_output(port = of.OFPP_FLOOD))
      msg.buffer_id = event.ofp.buffer_id
      msg.in_port = event.port
      self.connection.send(msg)

    def drop ():
      # Kill the buffer
      if event.ofp.buffer_id is not None:
        msg = of.ofp_packet_out()
        msg.buffer_id = event.ofp.buffer_id
        event.ofp.buffer_id = None # Mark is dead
        msg.in_port = event.port
        self.connection.send(msg)

    #log.debug("switch %i one packet in : %s",self.dpid, event.parsed)
    packet = event.parsed

    loc = (self, event.port) # Place we saw this ethaddr
    oldloc = mac_map.get(packet.src) # Place we last saw this ethaddr
    

    if packet.effective_ethertype == packet.LLDP_TYPE:
      drop()
      return
####should be modified because the last domain packet-in
    if oldloc is None:
      if packet.src.is_multicast == False:
        if loc[1] not in adjacency[loc[0]].values():
          mac_map[packet.src] = loc # Learn position for ethaddr
          log.debug("Learned %s at %s.%i", packet.src, loc[0], loc[1])
    elif oldloc != loc:
      # ethaddr seen at different place!
      if loc[1] not in adjacency[loc[0]].values():
        # New place is another "plain" port (probably)
        log.debug("%s moved from %s.%i to %s.%i?", packet.src,
                  dpid_to_str(oldloc[0].dpid), oldloc[1],
                  dpid_to_str(   loc[0].dpid),    loc[1])
        if packet.src.is_multicast == False:
          mac_map[packet.src] = loc # Learn position for ethaddr
          log.debug("Learned %s at %s.%i", packet.src, loc[0], loc[1])
      elif packet.dst.is_multicast == False:
        # ##New place is a switch-to-switch port!
        # Hopefully, this is a packet we're flooding because we didn't
        # know the destination, and not because it's somehow not on a
        # path that we expect it to be on.
        # If spanning_tree is running, we might check that this port is
        # on the spanning tree (it should be)
      #if packet.dst in mac_map:
        if packet.dst in mac_map:
          #
          #Unfortunately, we know the destination.  It's possible that
          # we learned it while it was in flight, but it's also possible
          # that something has gone wrong.
          log.debug("Cross-domain flow from %s arrive at the destination domain %s.%i\n",dpid_to_str(oldloc[0].dpid),dpid_to_str(self.dpid),event.port)
          
	  dest=mac_map[packet.dst]
	  match=of.ofp_match.from_packet(packet)
          fobj_in.write('Packet_in %s from %s arrived at destination domain %s.%i\n' % (packet.effective_ethertype,dpid_to_str(oldloc[0].dpid),dpid_to_str(self.dpid),event.port))
          r=[]
          r=_get_path(self,dest[0],event.port,dest[1])
          self._install_path(r,match,event.ofp)
          return
          '''if self.dpid/100==1:
            self.install_path_one(dest[0],dest[1],match,event,sws1)
            return
          elif self.dpid/100==2:
            self.install_path_one(dest[0],dest[1],match,event,sws2)
            return
          elif self.dpid/100==3:
            self.install_path_one(dest[0],dest[1],match,event,sws3)
            return'''
          '''log.warning("Packet from %s to known destination %s arrived "
                      "at %s.%i without flow", packet.src, packet.dst,
                      dpid_to_str(self.dpid), event.port)'''


    if packet.dst.is_multicast:
      if self.dpid == 316:
         log.debug("Flood multicast from %s at %s", packet.src,dpid_to_str(self.dpid))
      #log.debug("packet.dst is multicast !") #by lhc
      match = of.ofp_match.from_packet(packet)
      a = (match.wildcards,match.dl_vlan_pcp,match.dl_src,match.dl_dst,match.dl_vlan,match.dl_type,match.nw_proto,match.tp_src,match.tp_dst,match.in_port)
      #log.debug("buffer_packets[self.dpid].get(match): %s", buffer_packets[self.dpid].get(a))
      if buffer_packets.has_key(self.dpid):
        #log.debug("the num of buffer packets is %i,",len(buffer_packets[self.dpid]))
        if a in buffer_packets[self.dpid]:
          ##log.debug("drop a loop multicast packet!")
          drop()
        else:
          buffer_packets[self.dpid].append(a)
          ##log.debug("Flood multicast from %s", packet.src)
          flood()
      else:
        buffer_packets[self.dpid] = []
        buffer_packets[self.dpid].append(a)
        #log.debug("dpid: %s buffer a packet, match is %s!!",self.dpid,a)
        #log.debug("Flood multicast from %s", packet.src)
        flood()
      #flood()
    else:
      if packet.dst not in mac_map:
        match = of.ofp_match.from_packet(packet)
        a = (match.wildcards,match.dl_vlan_pcp,match.dl_src,match.dl_dst,match.dl_type,match.nw_proto,match.tp_src,match.tp_dst,match.in_port)
        #log.debug("buffer_packets[self.dpid].get(match): %s", buffer_packets[self.dpid].get(a))
        if buffer_packets.has_key(self.dpid):
          #log.debug("the num of buffer packets is %i,",len(buffer_packets[self.dpid]))
          if a in buffer_packets[self.dpid]:
            ##log.debug("drop a loop multicast packet!")
            drop()
        else:
          buffer_packets[self.dpid] = []
          buffer_packets[self.dpid].append(a)
          #log.debug("dpid: %s buffer a packet, match is %s!!",self.dpid,a)
          log.debug("%s unknown -- drop" % (packet.dst,))
          flood()
        #flood()
      else:
        ##intra domain routing
        dest=mac_map.get(packet.dst)
        srce=mac_map.get(packet.src)
        distance=100
	match=of.ofp_match.from_packet(packet)
        fobj_in.write('Packet_in %s from %s.%i arrived at source domain\n' % (packet.effective_ethertype,dpid_to_str(srce[0].dpid),event.port))
        if (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==1:
          log.debug("Intra domain route\n")
          self.install_path_one(dest[0],dest[1],match,event,sws1)
          return
        elif (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==2:
          log.debug("Intra domain route\n")
          self.install_path_one(dest[0],dest[1],match,event,sws2)
          return
        elif (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==3:
          log.debug("Intra domain route\n")
          self.install_path_one(dest[0],dest[1],match,event,sws3)
          return
        elif (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==4:
          log.debug("Intra domain route")
          self.install_path_one(dest[0],dest[1],match,event,sws4)
          return
        elif (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==5:
          log.debug("Intra domain route")
          self.install_path_one(dest[0],dest[1],match,event,sws5)
          return
        elif (dest[0].dpid/100)==(srce[0].dpid/100) and dest[0].dpid/100==6:
          log.debug("Intra domain route")
          self.install_path_one(dest[0],dest[1],match,event,sws6)
          return
        ##end pre routing
        #################################################
        #inter-routing
        log.debug("Inter domain route\n")
        ##determine path
        sws_b_path=[ ]
        sws_path=[]
        path=[]
        _calc_paths()
        print dest[0].dpid
        print srce[0].dpid
        if dest[0].dpid/100==1:
          print "dest in domain 1"
          des_sb=sws1_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws1_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]
        elif dest[0].dpid/100==2:
	  print "dest in domain 2"
          des_sb=sws2_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws2_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]
        elif dest[0].dpid/100==3:
 	  print "dest in domain 3" 
          des_sb=sws3_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws3_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]
        elif dest[0].dpid/100==4:
 	  print "dest in domain 4" 
          des_sb=sws4_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws4_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]
        elif dest[0].dpid/100==5:
 	  print "dest in domain 5" 
          des_sb=sws5_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws5_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]              
        elif dest[0].dpid/100==6:
 	  print "dest in domain 6" 
          des_sb=sws6_b[0]
          sws_path=[srce[0]]+_get_raw_path(srce[0],des_sb)+[des_sb]
          for j in sws6_b:
            path=[srce[0]]+_get_raw_path(srce[0],j)+[j]
            if len(sws_path)>len(path):
              sws_path=path
              path=[]
              
        ####source to the first border switch

        ##determine the border switch
        for j in sws_path:
          if j in sws_b:
            sws_b_path.append(j)
          else:
            continue
        ##install entries from the soure to the first border switch
        
        sws_first_switch=sws_b_path[0]
        sws_last_switch=sws_b_path[-1]
        
        ##self.install_path(dst_sw,final_outport,match,event)
        ##install entries that modify the packet destination address other than last border switch
        r=[]
        ##zhengxiang lujing
        for s1,s2 in zip(sws_b_path[:-1],sws_b_path[1:]):
          msg=of.ofp_flow_mod()
          my_match=of.ofp_match.from_packet(packet)
          my_match.dl_dst=None
          msg.match=my_match
          msg.idle_timeout = FLOW_IDLE_TIMEOUT
          msg.hard_timeout = FLOW_HARD_TIMEOUT
          r=[s1]+_get_raw_path(s1,s2)+[s2]
          out_port=adjacency[s1][r[1]]
          log.debug("%s switch adjacency %s switch port is %i\n",s1,s2,out_port)
          if s2== sws_last_switch:
            msg.actions.append(of.ofp_action_dl_addr.set_dst(packet.dst))
            msg.actions.append(of.ofp_action_output(port = out_port))
          else:
            msg.actions.append(of.ofp_action_dl_addr.set_dst(EthAddr(dpid_to_str(s2.dpid))))
            msg.actions.append(of.ofp_action_output(port = out_port))
          s1.connection.send(msg)
          #log.debug("%s msg is %s",s1, msg)
        print 'Install entries from the soure to the first border switch'
        r=[srce[0]]+_get_raw_path(srce[0],sws_first_switch)+[sws_first_switch]
        final_outport=adjacency[r[-2]][r[-1]]
        dst_sw=r[-2]
        r=[]
        r=_get_path(self,dst_sw,event.port,final_outport)
        self._install_path(r,match,event.ofp)
        return
        ##fangxiang lujing
        '''for s1,s2 in zip(sws_b_path[1:],sws_b_path[:-1]):
          msg=of.ofp_flow_mod()
          my_match=of.ofp_match.from_packet(packet)
          my_match.dl_dst=None
          msg.match=my_match
          msg.idle_timeout = FLOW_IDLE_TIMEOUT
          msg.hard_timeout = FLOW_HARD_TIMEOUT
          r=[s1]+_get_raw_path(s1,s2)+[s2]
          out_port=adjacency[s1][r[1]]
          log.debug("%s switch adjacency %s switch port is %i",s1,s2,out_port)
          if s2== sws_first_switch:
            msg.actions.append(of.ofp_action_dl_addr.set_dst(packet.src))
            msg.actions.append(of.ofp_action_output(port = out_port))
          else:
            msg.actions.append(of.ofp_action_dl_addr.set_dst(EthAddr(dpid_to_str(s2.dpid))))
            msg.actions.append(of.ofp_action_output(port = out_port))
          s1.connection.send(msg)
          log.debug("%s msg is %s",s1, msg)'''
        ##end

  def disconnect (self):
    if self.connection is not None:
      log.debug("Disconnect %s" % (self.connection,))
      self.connection.removeListeners(self._listeners)
      self.connection = None
      self._listeners = None

  def connect (self, connection):
    if self.dpid is None:
      self.dpid = connection.dpid
    assert self.dpid == connection.dpid
    if self.ports is None:
      self.ports = connection.features.ports
    self.disconnect()
    log.debug("Connect %s" % (connection,))
    self.connection = connection
    self._listeners = self.listenTo(connection)
    self._connected_at = time.time()

  @property
  def is_holding_down (self):
    if self._connected_at is None: return True
    if time.time() - self._connected_at > FLOOD_HOLDDOWN:
      return False
    return True

  def _handle_ConnectionDown (self, event):
    self.disconnect()


class l2_multi (EventMixin):

  _eventMixin_events = set([
    PathInstalled,
  ])

  def __init__ (self):
    # Listen to dependencies
    def startup ():
      core.openflow.addListeners(self, priority=0)
      core.openflow_discovery.addListeners(self)
    core.call_when_ready(startup, ('openflow','openflow_discovery'))

  def _handle_LinkEvent (self, event):
    def flip (link):
      return Discovery.Link(link[2],link[3], link[0],link[1])

    l = event.link
    sw1 = switches[l.dpid1]
    sw2 = switches[l.dpid2]

    # Invalidate all flows and path info.
    # For link adds, this makes sure that if a new link leads to an
    # improved path, we use it.
    # For link removals, this makes sure that we don't use a
    # path that may have been broken.
    # NOTE: This could be radically improved! (e.g., not *ALL* paths break)
    #clear = of.ofp_flow_mod(command=of.OFPFC_DELETE)
    #for sw in switches.itervalues():
    # if sw.connection is None: continue
    # sw.connection.send(clear)
    #path_map.clear()

    if event.removed:
      # This link no longer okay
      if sw2 in adjacency[sw1]: del adjacency[sw1][sw2]
      if sw1 in adjacency[sw2]: del adjacency[sw2][sw1]

      # But maybe there's another way to connect these...
      for ll in core.openflow_discovery.adjacency:
        if ll.dpid1 == l.dpid1 and ll.dpid2 == l.dpid2:
          if flip(ll) in core.openflow_discovery.adjacency:
            # Yup, link goes both ways
            adjacency[sw1][sw2] = ll.port1
            adjacency[sw2][sw1] = ll.port2
            # Fixed -- new link chosen to connect these
            break
    else:
      # If we already consider these nodes connected, we can
      # ignore this link up.
      # Otherwise, we might be interested...
      if adjacency[sw1][sw2] is None:
        # These previously weren't connected.  If the link
        # exists in both directions, we consider them connected now.
        if flip(l) in core.openflow_discovery.adjacency:
          # Yup, link goes both ways -- connected!
          adjacency[sw1][sw2] = l.port1
          adjacency[sw2][sw1] = l.port2

      # If we have learned a MAC on this port which we now know to
      # be connected to a switch, unlearn it.
      bad_macs = set()
      for mac,(sw,port) in mac_map.iteritems():
        if sw is sw1 and port == l.port1: bad_macs.add(mac)
        if sw is sw2 and port == l.port2: bad_macs.add(mac)
      for mac in bad_macs:
        log.debug("Unlearned %s", mac)
        del mac_map[mac]

  def _handle_ConnectionUp (self, event):
    sw = switches.get(event.dpid)
    ##dpid less 10 is border
    if sw is None:
      # New switch
      sw = Switch()
      switches[event.dpid] = sw
      sw.connect(event.connection)
      if event.dpid/100==1:
        sws1.append(sw)
        if event.dpid%100<=9:
          sws1_b.append(sw)      #border switch in domain1
          sws_b.append(sw)
      elif event.dpid/100==2:
        sws2.append(sw)
        if event.dpid%100<=9:
          sws2_b.append(sw)
          sws_b.append(sw)
      elif event.dpid/100==3:
        sws3.append(sw)
        if event.dpid%100<=9:
          sws3_b.append(sw)
          sws_b.append(sw)
      elif event.dpid/100==4:
        sws4.append(sw)
        if event.dpid%100<=9:
          sws4_b.append(sw)
          sws_b.append(sw)
      elif event.dpid/100==5:
        sws5.append(sw)
        if event.dpid%100<=9:
          sws5_b.append(sw)
          sws_b.append(sw)
      elif event.dpid/100==6:
        sws6.append(sw)
        if event.dpid%100<=9:
          sws6_b.append(sw)
          sws_b.append(sw)
    else:
      sw.connect(event.connection)

 # def _handle_BarrierIn (self, event):
  #  wp = waiting_paths.pop((event.dpid,event.xid), None)
 #   if not wp:
  #    #log.info("No waiting packet %s,%s", event.dpid, event.xid)
  #    return
  #  #log.debug("Notify waiting packet %s,%s", event.dpid, event.xid)
 #   wp.notify(event)


def launch ():
  core.registerNew(l2_multi)

  timeout = min(max(PATH_SETUP_TIME, 5) * 2, 15)
  Timer(timeout, WaitingPath.expire_waiting_paths, recurring=True)
  Timer(PREROUTE_START_TIME,_pre_route,recurring=False)
  Timer(CALC_PATHS_TIME,_calc_paths,recurring=False)
  Timer(_Del_Storm_Time_,_Timer_func,recurring=True)
