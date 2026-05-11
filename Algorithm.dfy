include "Graph.dfy"
include "Flow.dfy"
include "PushRelabel.dfy"

module Algorithm {
  import opened Graph
  import opened FlowGraph
  import opened PushRelabel

  class PushRelabelAlgorithm {
    const s: Node
    const t: Node
    const c: Capacity
    var f: Flow

    var e: Excess
    var d: Labeling
    var max_height: MaxHeight
    var buckets: Buckets

    constructor (s: Node, t: Node, c: Capacity)
      requires s != t
      ensures ValidWithPreflow()
    {
      this.s := s;
      this.t := t;
      this.c := c;

      new;

      buckets := seq(2 * V, _ => {});
      max_height := 0;

      for v := 0 to V
        // capacityConstraint
        invariant forall i: Node, j: Node | i < v :: f[i][j] <= c[i][j]

        // invariant to prove skewSymmetryConstraint
        invariant forall i: Node, j: Node | i < v :: f[i][j] == 0

        // invariant so Dafny does not forget
        invariant forall h: nat | 0 <= h < 2 * V :: |buckets[h]| == 0
      {
        for w := 0 to V
          // capacity constraint
          invariant forall i: Node, j: Node | i < v :: f[i][j] <= c[i][j]
          invariant forall j: Node | j < w :: f[v][j] <= c[v][j]

          // invariant to prove skewSymmetryConstraint
          invariant forall i: Node, j: Node | i < v :: f[i][j] == 0
          invariant forall j: Node | j < w :: f[v][j] == 0

          // invariant so Dafny does not forget
          invariant forall h: nat | 0 <= h < 2 * V :: |buckets[h]| == 0
        {
          f := f[v := f[v][w := 0]];
        }
      }
      assert ValidCapacityConstraint(c, f);

      assert forall i: Node, j: Node :: f[i][j] == 0;
      assert ValidSkewSymmetryConstraint(f);

      // assert by lemma
      assert ValidNonnegativityConstraint(s, f) by {
        forall v: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)} {
          Lemma_ZeroFlowHasZeroSum(f, v, V - 1);
        }
      }

      // needed to prove matching invariant on entry
      assert forall i: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, i, V - 1)} | i != s :: SumFlowInOnEdgesUpToEdgeUV(f, i, V - 1) == 0 by {
        forall v: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)} {
          Lemma_ZeroFlowHasZeroSum(f, v, V - 1);
        }
      }

      // for proving ValidBuckets(s, t, e, d, max_height, buckets) holds on entry
      assert forall h: nat | 0 <= h < 2 * V :: |buckets[h]| == 0;
      e := seq(V, _ => 0); // initialize excess to 0, will be overwritten in the loop
      assert forall v: Node :: e[v] == 0;

      for v := 0 to V
        invariant ValidCapacityConstraint(c, f)
        invariant ValidSkewSymmetryConstraint(f)
        invariant ValidNonnegativityConstraint(s, f)

        // for proving ValidExcess(s, f, e)
        invariant forall i: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, i, V - 1)} | i != s && i >= v ::
            SumFlowInOnEdgesUpToEdgeUV(f, i, V - 1) == 0
        invariant forall i: Node | i != s && i < v :: e[i] == SumFlowInOnEdgesUpToEdgeUV(f, i, V - 1)

        // invariant needed to prove f_old[s][i] == 0
        // which is needed for the call to Lemma_FlowSumAfterPush(f_old, f, s, v, delta, V - 1)
        invariant forall i: Node | i >= v :: f[s][i] == 0

        // for provid ValidLabeling(s, t, c, f, d)
        invariant forall i: Node | i != s && i < v :: d[i] == 0
        invariant forall i: Node | i != s && i < v :: ResidualCapacity(c, f, s, i) == 0

        // for proving ValidBuckets(s, t, e, d, max_height, buckets)
        invariant ValidBuckets(s, t, e, d, max_height, buckets)
        invariant forall h: nat, i: Node | 0 <= h < 2 * V && i >= v :: i !in buckets[h]
      {
        if (v == s) {
          continue;
        }

        // this initialization is mathematically equivalent to a push operation
        // we thus use the same lemma to prove ValidNonnegativityConstraint(s, f) as we use for the push operation
        ghost var f_old := f;
        var delta := c[s][v] as int;
        f := f[s := f[s][v := delta]];
        f := f[v := f[v][s := -delta]];
        Lemma_FlowSumAfterPush(f_old, f, s, v, delta, V - 1);
        assert ValidNonnegativityConstraint(s, f);

        assert ResidualCapacity(c, f, s, v) == 0;
        // assert that residual capacity of all nodes before v is unchanged
        assert forall i: Node | i != s && i < v :: ResidualCapacity(c, f, s, i) == ResidualCapacity(c, f_old, s, i);
        // which means it is also 0 (combining previous two assertions)
        assert forall i: Node | i != s && i < v + 1 :: ResidualCapacity(c, f, s, i) == 0;

        ghost var d_old := d;
        d := d[v := 0];

        assert SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1) == delta;
        ghost var e_old := e;
        e := e[v := delta];

        ghost var buckets_old := buckets;
        if (e[v] > 0 && v != t) {
          buckets := buckets[d[v] := buckets[d[v]] + {v}];
          if (d[v] > max_height) {
            max_height := d[v];
          }
        }
      }
      d := d[s := V];

      assert ValidWithPreflow();
    }

    predicate ValidWithPreflow()
      reads this
    {
      ValidPreflow(s, c, f) &&
      ValidExcess(s, f, e) &&
      ValidLabeling(s, t, c, f, d) &&
      ValidBuckets(s, t, e, d, max_height, buckets)
    }

    predicate ValidWithFlow()
      reads this
    {
      ValidFlow(s, t, c, f) &&
      ValidExcess(s, f, e) &&
      ValidLabeling(s, t, c, f, d) &&
      ValidBuckets(s, t, e, d, max_height, buckets)
    }

    method Push(v: Node, w: Node)
      requires ValidWithPreflow()

      // Preconditions for a valid push:
      requires v != s && v != t                 // v cannot be equal to the source or sink
      requires e[v] > 0                         // v must be active
      requires ResidualCapacity(c, f, v, w) > 0 // There must be residual capacity to move
      requires d[v] == d[w] + 1                 // Water must flow exactly one step downhill

      // postconditions
      ensures ValidWithPreflow()
      ensures max_height >= 0
      ensures max_height == old(max_height)
      ensures e[v] < old(e[v])
      ensures d == old(d)
      ensures buckets[d[v]] == old(buckets)[d[v]] || buckets[d[v]] == old(buckets)[d[v]] - {v}

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
      Lemma_FlowSumAfterPush(f_old, f, v, w, delta, V - 1);

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
      requires ValidWithPreflow()

      // Preconditions for a valid relabel:
      requires v != s && v != t // v cannot be equal to the source or sink
      requires e[v] > 0         // v must be active
      // v cannot be relabeled if it has a downhill neighbor
      requires forall w: Node | (ResidualCapacity(c, f, v, w) > 0) :: d[v] <= d[w]

      // Postconditions
      ensures ValidWithPreflow()
      ensures max_height >= 0
      ensures e == old(e)
      ensures d[v] > old(d[v])
      ensures forall i: Node | i != v :: d[i] == old(d)[i]

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

    method Discharge(v: Node)
      requires ValidWithPreflow()

      requires e[v] > 0
      requires v != s && v != t
      requires d[v] == max_height

      ensures ValidWithPreflow()
      ensures e[v] == 0
      ensures max_height >= 0

      ensures LabelingMetric(d, V) <= LabelingMetric(old(d), V)
      ensures d != old(d) ==> LabelingMetric(d, V) < LabelingMetric(old(d), V)
      ensures d == old(d) ==> (max_height == old(max_height) && |buckets[max_height]| < |old(buckets)[max_height]|)

      modifies this
    {
      ghost var start_d := d;
      ghost var start_buckets := buckets;
      ghost var start_max_height := max_height;

      while (e[v] > 0)
        invariant ValidWithPreflow()
        invariant max_height >= 0

        invariant LabelingMetric(d, V) <= LabelingMetric(start_d, V)
        invariant d != start_d ==> LabelingMetric(d, V) < LabelingMetric(start_d, V)
        invariant d == start_d ==> max_height == start_max_height
        invariant d == start_d ==> buckets[max_height] == start_buckets[max_height] || buckets[max_height] == start_buckets[max_height] - {v}

        decreases e[v] + (2*V - d[v])
      {
        if (exists w: Node :: ResidualCapacity(c, f, v, w) > 0 && d[v] == d[w] + 1) {
          var w: Node :| ResidualCapacity(c, f, v, w) > 0 && d[v] == d[w] + 1;
          Push(v, w);
        } else {
          ghost var d_before := d;
          Relabel(v);
          Lemma_LabelingMetricDecreases(d_before, d, v, V);
        }
      }

      assert d == start_d ==> buckets[max_height] == start_buckets[max_height] || buckets[max_height] == start_buckets[max_height] - {v};
      // because v is no longer active it cannot still be in the bucket
      assert d == start_d ==> buckets[max_height] == start_buckets[max_height] - {v};
      assert d == start_d ==> |buckets[max_height]| < |start_buckets[max_height]|;

      assert ValidWithPreflow();
    }

    method CalculateMaxFlow()
      requires ValidWithPreflow()
      ensures ValidWithFlow()

      modifies this
    {
      while (max_height >= 0)
        invariant ValidWithPreflow()

        decreases LabelingMetric(d, V), max_height
      {
        while (|buckets[max_height]| > 0)
          invariant ValidWithPreflow()
          invariant 0 <= max_height < 2 * V

          decreases LabelingMetric(d, V), max_height, |buckets[max_height]|
        {
          var v: Node :| v in buckets[max_height];
          Discharge(v);
        }

        max_height := max_height - 1;
      }

      // show dafny that ValidFLowConservationConstraint holds
      assert forall v: Node | v != s && v != t :: e[v] == 0;
      assert forall v: Node {:trigger SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1)} | (v != s && v != t) :: SumFlowInOnEdgesUpToEdgeUV(f, v, V - 1) == e[v];
      assert ValidFlowConservationConstraint(s, t, f);

      // assert that we have valid variables and a valid flow
      assert ValidWithFlow();

      // 2. Prove the Flow is Maximal!
      Lemma_NoResidualPathFromST(s, t, c, f, d);
      assert !(exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == s && p[|p|-1] == t);
      assert ValidFlow(s, t, c, f);
    }
  }
}