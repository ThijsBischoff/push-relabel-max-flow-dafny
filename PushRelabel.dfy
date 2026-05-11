include "Graph.dfy"
include "Flow.dfy"

module PushRelabel {
  import opened Graph
  import opened FlowGraph

  type Excess = e: seq<nat> | |e| == V witness seq(V, _ => 0)
  type Labeling = d: seq<nat> | |d| == V witness seq(V, _ => 0)
  type Buckets = b: seq<set<Node>> | |b| == 2 * V witness seq(2 * V, _ => {})
  type MaxHeight = max_height: int | -1 <= max_height < 2 * V witness -1

  predicate ValidExcess(s: Node, f: Flow, e: Excess)
  {
    forall v: Node | v != s :: e[v] == SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)
  }

  predicate ValidLabeling(s: Node, t: Node, c: Capacity, f: Flow, d: Labeling)
    requires ValidCapacityConstraint(c, f)
  {
    d[s] == V && d[t] == 0 &&
    (forall v: Node, w: Node | (ResidualCapacity(c, f, v, w) > 0) :: d[v] <= d[w] + 1) &&
    forall i: Node :: d[i] <= 2 * V
  }

  predicate ValidBuckets(s: Node, t: Node, e: Excess, d: Labeling, max_height: MaxHeight, buckets: Buckets)
  {
    // max_height is the upper bound
    (forall v: Node | (v != s && v != t && e[v] > 0) :: d[v] <= max_height) &&
    // If a non terminal node is active it must be in the bucket of its current height
    (forall v: Node | (v != s && v != t && e[v] > 0) :: v in buckets[d[v]]) &&
    // If a node is in a bucket it cannot be a terminal node
    (forall h: nat, v: Node | (0 <= h < 2 * V && v in buckets[h]) :: (v != s && v != t)) &&
    // If a node is in a bucket it must be active
    (forall h: nat, v: Node | (0 <= h < 2 * V && v != s && v != t && v in buckets[h]) :: (e[v] > 0)) &&
    // If a node is in a bucket it must have the height of that bucket
    (forall h: nat, v: Node | (0 <= h < 2 * V && v != s && v != t && v in buckets[h]) :: d[v] == h)
  }

  predicate ValidNonnegativityConstraint(s: Node, f: Flow)
  {
    forall v: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)} | v != s ::
      SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1) >= 0
  }

  predicate ValidPreflow(s: Node, c: Capacity, f: Flow)
  {
    ValidCapacityConstraint(c, f) && ValidSkewSymmetryConstraint(f) && ValidNonnegativityConstraint(s, f)
  }

  // used for proving termination
  ghost function LabelingMetric(d: Labeling, n: nat): nat
    requires n <= V
    requires forall i: Node :: d[i] <= 2 * V
    decreases n
  {
    if n == 0 then 0 else (2 * V - d[n-1]) + LabelingMetric(d, n-1)
  }

  // Proves to Dafny that if a single node goes UP, the overall metric goes DOWN
  lemma Lemma_LabelingMetricDecreases(d_old: Labeling, d_new: Labeling, v: Node, n: nat)
    requires n <= V
    requires forall i: Node :: d_old[i] <= 2 * V
    requires forall i: Node :: d_new[i] <= 2 * V
    requires forall i: Node | i != v :: d_new[i] == d_old[i]
    requires d_new[v] > d_old[v]

    ensures LabelingMetric(d_new, n) <= LabelingMetric(d_old, n)
    ensures v < n ==> LabelingMetric(d_new, n) < LabelingMetric(d_old, n)
    decreases n
  {
    if n > 0 { Lemma_LabelingMetricDecreases(d_old, d_new, v, n-1); }
  }

  lemma Lemma_FlowSumAfterPush(f_old: Flow, f_new: Flow, v: Node, w: Node, delta: int, N: nat)
    requires N < V

    // mutated flow on targeted edge
    requires f_new[v][w] == f_old[v][w] + delta
    requires f_new[w][v] == f_old[w][v] - delta

    // all other edges have the same flow
    requires forall x: Node, y: Node | ((x, y) != (v, w) && (x, y) != (w, v)) :: f_new[x][y] == f_old[x][y]

    // ensures all nodes that are not touched have the SumFlowIn
    ensures forall k: Node | k != v && k != w :: SumFlowInOnEdgesUpToEdgeUV(f_new, k, N) == SumFlowInOnEdgesUpToEdgeUV(f_old, k, N)
    // ensures SumFlowIn is correctly updated for v and w
    ensures SumFlowInOnEdgesUpToEdgeUV(f_new, v, N) == SumFlowInOnEdgesUpToEdgeUV(f_old, v, N) - (if N >= w then delta else 0)
    ensures SumFlowInOnEdgesUpToEdgeUV(f_new, w, N) == SumFlowInOnEdgesUpToEdgeUV(f_old, w, N) + (if N >= v then delta else 0)
  {
    if N == 0 {

    } else {
      Lemma_FlowSumAfterPush(f_old, f_new, v, w, delta, N - 1);
    }
  }

  lemma Lemma_ActiveVertexHasPathToSource(s: Node, t: Node, c: Capacity, f: Flow, e: Excess, v: Node)
    requires v != s && v != t
    requires e[v] > 0
    requires ValidPreflow(s, c, f)
    requires ValidExcess(s, f, e)
    ensures exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == v && p[|p|-1] == s

  lemma Lemma_PathTelescopingHeight(s: Node, t: Node, c: Capacity, f: Flow, d: Labeling, p: Path)
    requires |p| >= 1
    requires ValidPreflow(s, c, f)
    requires ValidLabeling(s, t, c, f, d)
    requires IsResidualPath(c, f, p)

    ensures d[p[0]] <= d[p[|p| - 1]] + |p| - 1

  lemma Lemma_NoResidualPathFromST(s: Node, t: Node, c: Capacity, f: Flow, d: Labeling)
    requires ValidPreflow(s, c, f)
    requires ValidLabeling(s, t, c, f, d)
    ensures !(exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == s && p[|p|-1] == t)
  {
    // Proof by contradiction
    if exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == s && p[|p|-1] == t {
      var p :| IsSimpleResidualPath(c, f, p) && p[0] == s && p[|p|-1] == t;

      Lemma_PathTelescopingHeight(s, t, c, f, d, p);
      assert d[p[0]] <= d[p[|p|-1]] + |p| - 1;
      assert d[s] == V && d[t] == 0;
      assert V <= 0 + |p| - 1;
      Lemma_SimplePathHasBoundedLength(p, V);
      assert |p| <= V;
      assert V <= V - 1;

      assert false;
    }
  }
}