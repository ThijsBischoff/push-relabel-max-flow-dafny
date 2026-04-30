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
    (forall v: Node, w: Node | (ResidualCapacity(c, f, v, w) > 0) :: d[v] <= d[w] + 1)
  }

  predicate ValidBuckets(s: Node, t: Node, e: Excess, d: Labeling, max_height: MaxHeight, buckets: Buckets)
  {
    // max_height is the upper bound
    (forall v: Node | (v != s && v != t && e[v] > 0) :: d[v] <= max_height) &&
    // If a non terminal node is active it must be in the bucket of its current height
    (forall v: Node | (v != s && v != t && e[v] > 0) :: v in buckets[d[v]]) &&
    // If a node is in a bucket it must be active and cannot be a terminal node
    (forall h: nat, v: Node | (0 <= h < 2 * V && v in buckets[h]) :: (e[v] > 0 && v != s && v != t)) &&
    // If a node is in a bucket it must have the height of that bucket
    (forall h: nat, v: Node | (0 <= h < 2 * V && v in buckets[h]) :: d[v] == h)
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

  lemma LemmaFlowSumAfterPush(f_old: Flow, f_new: Flow, v: Node, w: Node, delta: int, N: nat)
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
      LemmaFlowSumAfterPush(f_old, f_new, v, w, delta, N - 1);
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

  class PushRelabel {
    const s: Node
    const t: Node
    const c: Capacity
    var f: Flow

    var e: Excess
    var d: Labeling
    var max_height: MaxHeight
    var buckets: Buckets

    predicate Valid()
      reads this
    {
      ValidPreflow(s, c, f) &&
      ValidExcess(s, f, e) &&
      ValidLabeling(s, t, c, f, d) &&
      ValidBuckets(s, t, e, d, max_height, buckets)
    }

    method Push(v: Node, w: Node)
      requires Valid()

      // Preconditions for a valid push:
      requires v != s && v != t                 // v cannot be equal to the source or sink
      requires e[v] > 0                         // v must be active
      requires ResidualCapacity(c, f, v, w) > 0 // There must be pipe space
      requires d[v] == d[w] + 1                 // Water must flow exactly one step downhill

      // postconditions
      ensures Valid()

      modifies this
    {
      // Calculate how much water we can push
      var delta := e[v];
      var res_cap := ResidualCapacity(c, f, v, w);
      if (res_cap < delta) {
        delta := res_cap;
      }

      ghost var f_old := f;
      f := f[v := f[v][w := f[v][w] + delta]];
      f := f[w := f[w][v := f[w][v] - delta]];
      LemmaFlowSumAfterPush(f_old, f, v, w, delta, V - 1);

      // Store w's inital active state far later use
      var old_w_active: bool := e[w] > 0;

      e := e[v := e[v] - delta];
      e := e[w := e[w] + delta];

      // Update the Highest-Label Buckets
      // If v was active (precondition) and is now inactive, it leaves the buckets.
      if (e[v] == 0) {
        buckets := buckets[d[v] := buckets[d[v]] - {v}];
      }

      // If w was NOT active and w is not s or t, it enters the buckets.
      if (!old_w_active && w != s && w != t) {
        // w must be active now
        assert e[w] > 0;

        buckets := buckets[d[w] := buckets[d[w]] + {w}];
        // We don't need to update max_height here because water flows downhill
        // d[w] is strictly less than d[v], so it cannot become the new max_height.
      }
    }
    
    method Relabel(v: Node)
      requires Valid()

      // Preconditions for a valid relabel:
      requires v != s && v != t // v cannot be equal to the source or sink
      requires e[v] > 0         // v must be active
      // v cannot be relabeled if it has a downhill neighbor
      requires forall w: Node | (ResidualCapacity(c, f, v, w) > 0) :: d[v] <= d[w]

      // Postconditions
      ensures Valid()

      modifies this
    {
      // Find the lowest neighbor in the residual graph
      // We initialize minHeightNeighbour to an impossibly high value (2 * V)
      var minHeightNeighbour: nat := 2 * V;
      var w := 0;
      while (w < V)
        invariant 0 <= w <= V
        invariant minHeightNeighbour <= 2 * V
        invariant forall k: Node | k < w && (ResidualCapacity(c, f, v, k) > 0) :: minHeightNeighbour <= d[k]

        // Because v had no downhill neighbors, height[v] MUST be <= minHeightNeighbour.
        // invariant so that Dafny does not forget
        invariant d[v] <= minHeightNeighbour
      {
        if (ResidualCapacity(c, f, v, w) > 0) {
          if (d[w] < minHeightNeighbour) {
            minHeightNeighbour := d[w];
          }
        }
        w := w + 1;
      }
      // Assert minHeightNeighbour is actual minimum
      assert forall w: Node | (ResidualCapacity(c, f, v, w) > 0) :: minHeightNeighbour <= d[w];

      // ------ Lemma's and proofs needed to prove height[v] < 2 * V after relabel ------
      // Prove a path to source exists from v
      Lemma_ActiveVertexHasPathToSource(s, t, c, f, e, v);
      // Extract that path
      ghost var pathToSource :| IsSimpleResidualPath(c, f, pathToSource) && pathToSource[0] == v && pathToSource[|pathToSource|-1] == s;

      // Since v != s, the path has at least 2 nodes. Grab the next node in the path
      assert |pathToSource| >= 2;
      ghost var pathToSourceNextNode := pathToSource[1];

      // Because v and pathToSourceNextNode are connected on a residual path, there is residual capacity
      assert ResidualCapacity(c, f, v, pathToSourceNextNode) > 0;

      // get the remainder of the path (from pathToSourceNextNode to s)
      ghost var pathToSourceWithoutV := pathToSource[1..];

      // Apply length and telescoping height lemmas
      Lemma_SimplePathHasBoundedLength(pathToSource);
      assert |pathToSource| <= V;
      Lemma_PathTelescopingHeight(s, t, c, f, d, pathToSourceWithoutV);
      assert d[pathToSourceNextNode] <= d[s] + |pathToSourceWithoutV| - 1;
      assert d[pathToSourceNextNode] <= V + (V - 1) - 1; // Since height[s] == V && ((|pathToSource| <= V) ==> (|pathToSourceWithoutV| <= V - 1))
      assert d[pathToSourceNextNode] <= 2 * V - 2;
      assert d[pathToSourceNextNode] < 2 * V - 1;

      // This proves there exists a path to source where height[pathToSourceNextNode] < 2 * V - 1
      // minHeightNeighbour is the neighbour on the path where the next node has the minimum height
      // this means the following assertions also holds
      assert minHeightNeighbour < 2 * V - 1;
      assert minHeightNeighbour + 1 < 2 * V;
      // ------------

      buckets := buckets[d[v] := buckets[d[v]] - {v}];

      d := d[v := minHeightNeighbour + 1];

      buckets := buckets[d[v] := buckets[d[v]] + {v}];

      if (d[v] > max_height) {
        max_height := d[v];
      }
    }
  }
}