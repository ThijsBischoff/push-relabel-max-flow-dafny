include "Graph.dfy"

module FlowGraph {
  import opened Graph

  type Capacity = c: seq<seq<nat>> | |c| == V && forall i :: 0 <= i < |c| ==> |c[i]| == V witness seq(V, _ => seq(V, _ => 0))
  type Flow = f: seq<seq<int>> | |f| == V && forall i :: 0 <= i < |f| ==> |f[i]| == V witness seq(V, _ => seq(V, _ => 0))

  predicate ValidCapacityConstraint(c: Capacity, f: Flow)
  {
    forall v: Node, w: Node :: (f[v][w] <= c[v][w])
  }

  predicate ValidSkewSymmetryConstraint(f: Flow)
  {
    forall v: Node, w: Node :: (f[v][w] == -f[w][v])
  }

  predicate ValidFlowConservationConstraint(s: Node, t: Node, f: Flow)
  {
    forall v: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)} ::
      (v != s && v != t) ==> (SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1) == 0)
  }

  // Computes the sum of flow into node 'v' on edges from (0, v) up to edge ('u', v)
  function SumFlowInOnEdgesUpToEdgeUV(f: Flow, v: Node, u: nat): int
    requires u < V
    decreases u
  {
    if u == 0 then
      f[0][v]
    else
      f[u][v] + SumFlowInOnEdgesUpToEdgeUV(f, v, u-1)
  }

  function ResidualCapacity(c: Capacity, f: Flow, v: Node, w: Node): nat
    requires ValidCapacityConstraint(c, f)
  {
    c[v][w] - f[v][w]
  }

  predicate ValidFlow(s: Node, t: Node, c: Capacity, f: Flow)
  {
    ValidCapacityConstraint(c, f) && ValidSkewSymmetryConstraint(f) && ValidFlowConservationConstraint(s, t, f)
  }

  predicate IsResidualPath(c: Capacity, f: Flow, p: Path)
    requires ValidCapacityConstraint(c, f)
  {
    forall i | (0 <= i < |p| - 1) :: (ResidualCapacity(c, f, p[i], p[i+1]) > 0)
  }

  predicate IsSimpleResidualPath(c: Capacity, f: Flow, p: Path)
    requires ValidCapacityConstraint(c, f)
  {
    IsResidualPath(c, f, p) && IsSimplePath(p)
  }
  
  lemma Lemma_ZeroFlowHasZeroSum(f: Flow, v: Node, u: nat)
    requires u < V
    requires forall i: Node, j: Node :: f[i][j] == 0
    ensures SumFlowInOnEdgesUpToEdgeUV(f, v, u) == 0
  {
    // automatically verified by Dafny
  }
}