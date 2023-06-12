-- Author: Alistair Geesing

import Lean

namespace Hammer.PS

open Lean


structure NameDiGraph where
  nodes : NameSet
  outgoing : NameMap NameSet
  incoming : NameMap NameSet

instance : EmptyCollection NameDiGraph where
  emptyCollection := { nodes := ∅, incoming := ∅, outgoing := ∅ }

instance : Inhabited NameDiGraph where
  default := ∅

def NameDiGraph.containsNode (graph : NameDiGraph) (node : Name) : Bool :=
  graph.nodes.contains node

def NameDiGraph.insertNode (graph : NameDiGraph) (node : Name) : NameDiGraph :=
  assert! ¬(graph.containsNode node)
  { graph with nodes := graph.nodes.insert node }

def NameDiGraph.containsEdge (graph : NameDiGraph) (src dst : Name) : Bool :=
  graph.outgoing.findD src ∅ |>.contains dst

def NameDiGraph.insertEdge (graph : NameDiGraph) (src dst : Name) : NameDiGraph := Id.run do
  if ¬graph.containsNode src then
    panic! "Attempting to insert edge " ++ src.toString ++ " -> " ++ dst.toString ++ " but " ++ src.toString ++ " does not exist"
  if ¬graph.containsNode dst then
    panic! "Attempting to insert edge " ++ src.toString ++ " -> " ++ dst.toString ++ " but " ++ dst.toString ++ " does not exist"
  assert! graph.containsNode src
  assert! graph.containsNode dst
  assert! !(graph.containsEdge src dst)
  {
    nodes := graph.nodes
    outgoing := graph.outgoing.insert src $ graph.outgoing.findD src ∅ |>.insert dst
    incoming := graph.incoming.insert dst $ graph.incoming.findD dst ∅ |>.insert src
  }

def NameDiGraph.eraseEdge (graph : NameDiGraph) (src dst : Name) : NameDiGraph :=
  assert! graph.outgoing.contains src && (graph.outgoing.find! src |>.contains dst)
  assert! graph.incoming.contains dst && (graph.incoming.find! dst |>.contains src)
  {
    nodes := graph.nodes
    outgoing :=
      let outgoing_src := graph.outgoing.find! src |>.erase dst
      if outgoing_src.size > 0
        then graph.outgoing.insert src outgoing_src
        else graph.outgoing.erase src
    incoming :=
      let incoming_dst := graph.incoming.find! dst |>.erase src
      if incoming_dst.size > 0
        then graph.incoming.insert dst incoming_dst
        else graph.incoming.erase dst
  }

def NameDiGraph.hasEdges (graph : NameDiGraph) : Bool :=
  ¬graph.outgoing.isEmpty ∨ ¬graph.incoming.isEmpty

def NameDiGraph.hasIncomingEdges (graph : NameDiGraph) (n : Name) : Bool :=
  assert! graph.nodes.contains n
  graph.incoming.contains n

def NameDiGraph.reverseEdges (graph : NameDiGraph) : NameDiGraph :=
  { graph with incoming := graph.outgoing, outgoing := graph.incoming }


structure GraphCycles where
  outgoing : NameMap NameSet

instance : ToString GraphCycles where
  toString := λgraphCycles => Id.run do
    let mut edges := []
    for (a, bs) in graphCycles.outgoing do
      for b in bs do
        edges := edges ++ [a.toString ++ " -> " ++ b.toString]

    return "Graph contains cycles (" ++ (edges.intersperse ", " |>.foldl (.++.) "") ++ ")"


namespace KahnImpl

structure State where
  graph : NameDiGraph
  S : Array Name
  L : Array Name

abbrev KahnM := StateM State

def initState (graph : NameDiGraph) : State := {
  graph
  S := graph.nodes.fold (λS node => if ¬graph.hasIncomingEdges node then S.push node else S) ∅
  L := ∅
}

partial def kahn : KahnM (Except GraphCycles (Array Name)) := do
  let n? ← modifyGet λs => (s.S.back?, { s with S := s.S.pop })
  let n ← match n? with
  | some n => pure n
  | none => do
    if (←get).graph.hasEdges then
      return .error { outgoing := (←get).graph.outgoing }
    return .ok (←get).L

  modify λs => { s with L := s.L.push n }

  for m in (←get).graph.outgoing.findD n ∅ do
    modify λs => { s with graph := s.graph.eraseEdge n m }
    if ¬(←get).graph.hasIncomingEdges m then
      modify λs => { s with S := s.S.push m }

  kahn

end KahnImpl

def topologicalSort (graph : NameDiGraph) : Except GraphCycles (Array Name) :=
  KahnImpl.kahn |>.run' (KahnImpl.initState graph.reverseEdges)
