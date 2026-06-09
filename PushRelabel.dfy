include "Graph.dfy"
include "Flow.dfy"

module PushRelabel {
  import opened Graph
  import opened FlowGraph

  type Excess = e: seq<nat> | |e| == V witness seq(V, _ => 0)
  type Labeling = d: seq<nat> | |d| == V witness seq(V, _ => 0)
  type Buckets = b: seq<set<Node>> | |b| == 2 * V witness seq(2 * V, _ => {})
  type MaxHeight = max_height: int | -1 <= max_height < 2 * V witness -1

  // used for proving termination
  ghost function LabelingMetric(d: Labeling, n: nat): nat
    requires n <= V
    requires forall i: Node :: d[i] <= 2 * V
    decreases n
  {
    if n == 0 then 0 else (2 * V - d[n-1]) + LabelingMetric(d, n-1)
  }

  function TotalExcessOfSet(e: Excess, S: set<Node>, maxNode: nat): int
    requires maxNode < V
    decreases maxNode
  {
    (if maxNode in S then e[maxNode] else 0) +
    (if maxNode == 0 then 0 else TotalExcessOfSet(e, S, maxNode - 1))
  }

  predicate ValidExcess(s: Node, f: Flow, e: Excess)
  {
    forall v: Node | v != s :: e[v] == SumTotalFlowToNode(f, v, V - 1)
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
    forall v: Node {:trigger SumTotalFlowToNode(f, v, V - 1)} | v != s ::
      SumTotalFlowToNode(f, v, V - 1) >= 0
  }

  predicate ValidPreflow(s: Node, c: Capacity, f: Flow)
  {
    ValidCapacityConstraint(c, f) && ValidSkewSymmetryConstraint(f) && ValidNonnegativityConstraint(s, f)
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

    // ensures all nodes that are not touched have the same SumFlowIn
    ensures forall k: Node | k != v && k != w :: SumTotalFlowToNode(f_new, k, N) == SumTotalFlowToNode(f_old, k, N)
    // ensures SumFlowIn is correctly updated for v and w
    ensures SumTotalFlowToNode(f_new, v, N) == SumTotalFlowToNode(f_old, v, N) - (if N >= w then delta else 0)
    ensures SumTotalFlowToNode(f_new, w, N) == SumTotalFlowToNode(f_old, w, N) + (if N >= v then delta else 0)
  {
    if N == 0 {

    } else {
      Lemma_FlowSumAfterPush(f_old, f_new, v, w, delta, N - 1);
    }
  }

  lemma Lemma_PathTelescopingHeight(s: Node, t: Node, c: Capacity, f: Flow, d: Labeling, p: Path)
    requires |p| >= 1
    requires ValidPreflow(s, c, f)
    requires ValidLabeling(s, t, c, f, d)
    requires IsResidualPath(c, f, p)

    ensures d[p[0]] <= d[p[|p| - 1]] + |p| - 1
  {
    if |p| == 1 {
      // automatically verified by Dafny
    } else {
      var p' := p[..|p|-1]; // remove the last element
      assert |p'| == |p| - 1;

      Lemma_PathTelescopingHeight(s, t, c, f, d, p'); // show dafny the lemma holds for p'
    }
  }

  lemma Lemma_NoResidualPathFromSToT(s: Node, t: Node, c: Capacity, f: Flow, d: Labeling)
    requires ValidPreflow(s, c, f)
    requires ValidLabeling(s, t, c, f, d)
    ensures !ResidualPathExists(c, f, s, t)
  {
    // Proof by contradiction
    if ResidualPathExists(c, f, s, t) {
      var p: Path :| IsResidualPath(c, f, p) && p[0] == s && p[|p|-1] == t;

      while !IsSimplePath(p)
        invariant IsResidualPath(c, f, p)
        invariant p[0] == s && p[|p|-1] == t
        decreases |p|
      {
        var i, j :| 0 <= i < j < |p| && p[i] == p[j];
        p := p[..i] + p[j..];
      }
      assert IsSimplePath(p);

      Lemma_PathTelescopingHeight(s, t, c, f, d, p);
      assert d[p[0]] <= d[p[|p| - 1]] + |p| - 1;
      assert d[s] == V && d[t] == 0;
      assert V <= 0 + |p| - 1;
      Lemma_SimplePathHasBoundedLength(p, V);
      assert |p| <= V;
      assert V <= V - 1;

      assert false;
    }
  }

  lemma Lemma_TotalExcessOfSetIncludingActiveNodeIsStrictlyPositive(e: Excess, S: set<Node>, maxNode: nat, v: Node)
    requires maxNode < V
    requires v in S && e[v] > 0
    requires forall u: Node | u in S :: e[u] >= 0
    ensures if v <= maxNode then TotalExcessOfSet(e, S, maxNode) > 0 else TotalExcessOfSet(e, S, maxNode) >= 0
    decreases maxNode
  {
    // automatic induction by Dafny
  }

  lemma Lemma_TotalExcessOfSetEqualsSumIncomingFlowOfSet(s: Node, e: Excess, f: Flow, S: set<Node>, maxNode: nat)
    requires maxNode < V
    requires ValidExcess(s, f, e)
    requires s !in S
    ensures TotalExcessOfSet(e, S, maxNode) == SumIncomingFlowOfSet(f, S, V - 1, maxNode)
    decreases maxNode
  {
    if maxNode > 0 { Lemma_TotalExcessOfSetEqualsSumIncomingFlowOfSet(s, e, f, S, maxNode - 1); }
    // intuition: Excess of a node is defined (in ValidExcess) as the sum of incomming flow, trivially this holds for a set of nodes as well.
  }

  lemma Lemma_ActiveNodeHasPathToSource(s: Node, t: Node, c: Capacity, f: Flow, e: Excess, v: Node)
    requires v != s && v != t
    requires e[v] > 0
    requires ValidPreflow(s, c, f) && ValidExcess(s, f, e)
    ensures exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == v && p[|p|-1] == s
  {
    var S := NodesReachableFrom(c, f, v);

    // Trivially, v is reachable from itself
    assert IsSimpleResidualPath(c, f, [v]);
    assert v in S;

    // Prove s in S by contradiction
    assert s in S by {
      if s !in S {
        // All nodes in the reachable set must have non-negative excess
        assert ValidNonnegativityConstraint(s, f);
        forall u: Node | u in S ensures e[u] >= 0 {}

        // Since v has positive excess and is in S, the entire set's excess is strictly positive (> 0)
        Lemma_TotalExcessOfSetIncludingActiveNodeIsStrictlyPositive(e, S, V - 1, v);
        assert TotalExcessOfSet(e, S, V - 1) > 0;

        // Prove the Total Excess equals the Total Flow entering the set
        Lemma_TotalExcessOfSetEqualsSumIncomingFlowOfSet(s, e, f, S, V - 1);
        Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet(f, S, V - 1, V - 1);

        // Decompose the Flow into Internal (From S to S) and External (From outside S to S)
        Lemma_SumFlowFromAllNodesEqualsSumInternalFlowPlusSumExternalFlow(f, S, V - 1, V - 1);

        // Prove internal flow cancels itself out to 0 (Skew Symmetry)
        Lemma_TotalInternalFlowOfSetIsZero(f, S, V - 1);

        // Prove external flow <= 0
        Lemma_TotalExternalFlowOfReachableSetIsNonPositive(c, f, v, S, V - 1, V - 1);

        // Excess (> 0) is equal to the Flow, which is equal to internal flow (0) + external flow (<= 0).
        // 0 < (0 + (<= 0)) --> 0 < 0 --> contradiction
        assert false;
      }
    }

    assert exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == v && p[|p|-1] == s;
  }
}