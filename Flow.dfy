include "Graph.dfy"

module FlowGraph {
  import Graph

  predicate ValidFlowMatrixShape(V: nat, flow: array2<nat>)
  {
    flow.Length0 == V && flow.Length1 == V
  }

  predicate ValidCapacityMatrixShape(V: nat, capacity: array2<nat>)
  {
    capacity.Length0 == V &&
    capacity.Length1 == V
  }

  predicate ValidExcessShape(V: nat, excess: array<int>)
  {
    excess.Length == V
  }

  predicate ValidHeightShape(V: nat, height: array<nat>)
  {
    height.Length == V
  }

  predicate NodeIsActive(V: nat, u: nat, excess: array<int>)
    reads excess
    requires Graph.ValidNode(V, u)
    requires ValidExcessShape(V, excess)
  {
    excess[u] > 0
  }

  predicate NodeIsSourceOrSink(u: nat, s: nat, t: nat)
  {
    u == s || u == t
  }

  function ResidualCapacity(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, u: nat, v: nat): nat
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    capacity[u, v] - flow[u, v] + flow[v, u]
  }

  predicate EdgeInResidual(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, u: nat, v: nat)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    ResidualCapacity(V, s, t, capacity, flow, u, v) > 0
  }

  predicate ValidFlow(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
  {
    forall u, v :: (0 <= u < V && 0 <= v < V) ==>
                     (0 <= flow[u, v] <= capacity[u, v])
  }

  predicate ValidPreflow(V: nat, s: nat, t: nat, excess: array<int>)
    reads excess
    requires Graph.ValidGraph(V, s, t)
    requires ValidExcessShape(V, excess)
  {
    forall u :: (0 <= u < V && !NodeIsSourceOrSink(u, s, t)) ==> excess[u] >= 0
  }

  predicate ValidLabeling(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, height: array<nat>)
    reads capacity, flow, height
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidHeightShape(V, height)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    height[s] == V &&
    height[t] == 0 &&
    (forall u, v :: (0 <= u < V && 0 <= v < V && EdgeInResidual(V, s, t, capacity, flow, u, v)) ==>
                      (height[u] <= height[v] + 1))
  }

  predicate IsResidualPath(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, p: seq<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    |p| > 0 &&
    (forall i :: (0 <= i < |p|) ==>
                   (Graph.ValidNode(V, p[i]))) &&
    (forall i :: (0 <= i < |p| - 1) ==>
                   (EdgeInResidual(V, s, t, capacity, flow, p[i], p[i+1])))
  }

  predicate IsSimpleResidualPath(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, p: seq<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    IsResidualPath(V, s, t, capacity, flow, p) && Graph.NodeSequenceHasNoDuplicates(p)
  }

  lemma Lemma_ActiveNodeHasPathToSource(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, excess: array<int>, u: nat)
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidExcessShape(V, excess)
    requires ValidPreflow(V, s, t, excess)
    requires Graph.ValidNode(V, u) && !NodeIsSourceOrSink(u, s, t)
    requires NodeIsActive(V, u, excess)
    requires ValidFlow(V, s, t, capacity, flow)
    ensures exists p :: IsSimpleResidualPath(V, s, t, capacity, flow, p) && p[0] == u && p[|p|-1] == s

  lemma Lemma_PathTelescopingHeight(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, height: array<nat>, p: seq<nat>)
    requires |p| >= 1
    requires Graph.ValidNode(V, p[0]) && Graph.ValidNode(V, p[|p| - 1])
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidHeightShape(V, height)
    requires ValidFlow(V, s, t, capacity, flow)
    requires ValidLabeling(V, s, t, capacity, flow, height)

    requires IsResidualPath(V, s, t, capacity, flow, p)

    ensures height[p[0]] <= height[p[|p| - 1]] + |p| - 1
}