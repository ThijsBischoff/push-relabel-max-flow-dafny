include "Graph.dfy"

module FlowGraph {
  import Graph

  predicate ValidFlowMatrixShape(V: nat, flow: array2<int>)
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

  predicate NodeIsActive(V: nat, v: nat, excess: array<int>)
    reads excess
    requires Graph.ValidNode(V, v)
    requires ValidExcessShape(V, excess)
  {
    excess[v] > 0
  }

  predicate NodeIsSourceOrSink(v: nat, s: nat, t: nat)
  {
    v == s || v == t
  }

  function ResidualCapacity(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, v: nat, w: nat): nat
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires Graph.ValidNode(V, v) && Graph.ValidNode(V, w)
    requires ValidPreflow(V, s, t, capacity, flow)
  {
    capacity[v, w] - flow[v, w]
  }

  predicate EdgeInResidual(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, v: nat, w: nat)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires Graph.ValidNode(V, v) && Graph.ValidNode(V, w)
    requires ValidPreflow(V, s, t, capacity, flow)
  {
    ResidualCapacity(V, s, t, capacity, flow, v, w) > 0
  }

  predicate ValidCapacityConstraint(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
  {
    (forall v, w :: (0 <= v < V && 0 <= w < V) ==>
                      (flow[v, w] <= capacity[v, w]))
  }

  predicate ValidSkewSymmetryConstraint(V: nat, s: nat, t: nat, flow: array2<int>)
    reads flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
  {
    (forall v, w :: (0 <= v < V && 0 <= w < V) ==>
                      (flow[v, w] == -flow[w, v]))
  }

  // Computes the sum of flow into vertex 'v' on edges from (0, v) up to edge ('u-1', v)
  function SumFlowIn(V: nat, flow: array2<int>, v: nat, u: nat): int
    reads flow
    requires ValidFlowMatrixShape(V, flow)
    requires Graph.ValidNode(V, v)
    requires u <= V
    decreases u
  {
    if u == 0 then
      0
    else
      flow[u-1, v] + SumFlowIn(V, flow, v, u-1)
  }

  predicate ValidFlowConservationConstraint(V: nat, s: nat, t: nat, flow: array2<int>)
    reads flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
  {
    (forall v :: (0 <= v < V && !NodeIsSourceOrSink(v, s, t)) ==> (SumFlowIn(V, flow, v, V) == 0))
  }

  predicate ValidNonnegativityConstraint(V: nat, s: nat, t: nat, flow: array2<int>)
    reads flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
  {
    (forall v :: (0 <= v < V && v != s) ==> (SumFlowIn(V, flow, v, V) >= 0))
  }


  predicate ValidFlow(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
  {
    ValidCapacityConstraint(V, s, t, capacity, flow) && ValidSkewSymmetryConstraint(V, s, t, flow) && ValidFlowConservationConstraint(V, s, t, flow)
  }

  predicate ValidPreflow(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
  {
    ValidCapacityConstraint(V, s, t, capacity, flow) && ValidSkewSymmetryConstraint(V, s, t, flow) && ValidNonnegativityConstraint(V, s, t, flow)
  }

  predicate ValidExcess(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, excess: array<int>)
    reads capacity, excess, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidPreflow(V, s, t, capacity, flow)
    requires ValidExcessShape(V, excess)
  {
    forall v :: (0 <= v < V) ==> (excess[v] == SumFlowIn(V, flow, v, V))
  }

  predicate ValidLabeling(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, height: array<nat>)
    reads capacity, flow, height
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidHeightShape(V, height)
    requires ValidPreflow(V, s, t, capacity, flow)
  {
    height[s] == V &&
    height[t] == 0 &&
    (forall v, w :: (0 <= v < V && 0 <= w < V && EdgeInResidual(V, s, t, capacity, flow, v, w)) ==>
                      (height[v] <= height[w] + 1))
  }

  predicate IsResidualPath(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, p: seq<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidPreflow(V, s, t, capacity, flow)
  {
    |p| > 0 &&
    (forall i :: (0 <= i < |p|) ==>
                   (Graph.ValidNode(V, p[i]))) &&
    (forall i :: (0 <= i < |p| - 1) ==>
                   (EdgeInResidual(V, s, t, capacity, flow, p[i], p[i+1])))
  }

  predicate IsSimpleResidualPath(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, p: seq<nat>)
    reads capacity, flow
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidPreflow(V, s, t, capacity, flow)
  {
    IsResidualPath(V, s, t, capacity, flow, p) && Graph.NodeSequenceHasNoDuplicates(p)
  }

  twostate lemma LemmaFlowSumAfterPush(V: nat, flow: array2<int>, v: nat, w: nat, delta: int, N: nat)
    requires ValidFlowMatrixShape(V, flow)
    requires Graph.ValidNode(V, v) && Graph.ValidNode(V, w) && N <= V

    // mutated flow on targeted edge
    requires flow[v, w] == old(flow[v, w]) + delta
    requires flow[w, v] == old(flow[w, v]) - delta

    // all other edges have the same flow
    requires forall x, y :: (0 <= x < V && 0 <= y < V && (x, y) != (v, w) && (x, y) != (w, v)) ==> (flow[x, y] == old(flow[x, y]))

    // ensures all nodes that are not touched have the SumFlowIn
    ensures forall k :: (0 <= k < V && k != v && k != w) ==> (SumFlowIn(V, flow, k, N) == old(SumFlowIn(V, flow, k, N)))
    // ensures SumFlowIn is correctly updated for v and w
    ensures SumFlowIn(V, flow, v, N) == old(SumFlowIn(V, flow, v, N)) - (if N > w then delta else 0)
    ensures SumFlowIn(V, flow, w, N) == old(SumFlowIn(V, flow, w, N)) + (if N > v then delta else 0)
  {
    if N == 0 {

    } else {
      LemmaFlowSumAfterPush(V, flow, v, w, delta, N - 1);
    }
  }

  lemma Lemma_ActiveVertexHasPathToSource(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, excess: array<int>, v: nat)
    requires Graph.ValidGraph(V, s, t)
    requires Graph.ValidNode(V, v) && !NodeIsSourceOrSink(v, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidExcessShape(V, excess)
    requires ValidPreflow(V, s, t, capacity, flow)
    requires ValidExcess(V, s, t, capacity, flow, excess)
    requires NodeIsActive(V, v, excess)
    ensures exists p :: IsSimpleResidualPath(V, s, t, capacity, flow, p) && p[0] == v && p[|p|-1] == s

  lemma Lemma_PathTelescopingHeight(V: nat, s: nat, t: nat, capacity: array2<nat>, flow: array2<int>, height: array<nat>, p: seq<nat>)
    requires |p| >= 1
    requires Graph.ValidNode(V, p[0]) && Graph.ValidNode(V, p[|p| - 1])
    requires Graph.ValidGraph(V, s, t)
    requires ValidFlowMatrixShape(V, flow)
    requires ValidCapacityMatrixShape(V, capacity)
    requires ValidHeightShape(V, height)
    requires ValidPreflow(V, s, t, capacity, flow)
    requires ValidLabeling(V, s, t, capacity, flow, height)

    requires IsResidualPath(V, s, t, capacity, flow, p)

    ensures height[p[0]] <= height[p[|p| - 1]] + |p| - 1
}