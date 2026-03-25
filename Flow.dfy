include "Graph.dfy"

module FlowGraph {
  import Graph

  predicate ValidFlowMatrixShape(V: nat, flow: array2<nat>)
    reads flow
  {
    flow.Length0 == V && flow.Length1 == V
  }

  predicate ValidExcessShape(V: nat, excess: array<int>)
    reads excess
  {
    excess.Length == V
  }

  predicate ValidHeightShape(V: nat, height: array<nat>)
    reads height
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


  function ResidualCapacity(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, u: nat, v: nat): nat
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t, capacity)
    requires ValidFlowMatrixShape(V, flow)
    requires Graph.ValidEdge(V, u, v)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    capacity[u, v] - flow[u, v] + flow[v, u]
  }

  predicate EdgeInResidual(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, u: nat, v: nat)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t, capacity)
    requires ValidFlowMatrixShape(V, flow)
    requires Graph.ValidEdge(V, u, v)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    ResidualCapacity(V, s, t, capacity, flow, u, v) > 0
  }

  predicate ValidFlow(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t, capacity)
    requires ValidFlowMatrixShape(V, flow)
  {
    forall u, v :: 0 <= u < V && 0 <= v < V ==>
                     0 <= flow[u, v] <= capacity[u, v]
  }

  predicate ValidPreflow(V: nat, s: nat, t: nat, capacity: array2<nat>, excess: array<int>)
    reads capacity, excess
    requires Graph.ValidGraph(V, s, t, capacity)
    requires ValidExcessShape(V, excess)
  {
    forall u :: 0 <= u < V && u != s && u != t ==> excess[u] >= 0
  }

  predicate ValidLabeling(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<nat>, height: array<nat>)
    reads capacity, flow, height
    requires Graph.ValidGraph(V, s, t, capacity)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidHeightShape(V, height)
    requires ValidFlow(V, s, t, capacity, flow)
  {
    height[s] == V &&
    height[t] == 0 &&
    (forall u, v :: 0 <= u < V && 0 <= v < V && EdgeInResidual(V, s, t, capacity, flow, u, v) ==>
                      height[u] <= height[v] + 1)
  }
}