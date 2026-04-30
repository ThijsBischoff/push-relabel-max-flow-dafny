include "Graph.dfy"
include "Flow.dfy"

module Algorithm {
  import Graph
  import FlowGraph

  class PushRelabel {
    const V: nat
    const s: nat
    const t: nat
    const capacity: array2<nat>

    var flow: array2<int>
    var height: array<nat>
    var excess: array<int>

    var buckets: array<set<nat>>
    var max_height: int

    predicate ValidBucketsStructure()
      reads this
    {
      buckets.Length == 2 * V
    }

    predicate ValidBuckets()
      reads this, height, excess, buckets
      requires FlowGraph.ValidHeightShape(V, height)
      requires FlowGraph.ValidExcessShape(V, excess)
      requires ValidBucketsStructure()
    {
      -1 <= max_height < 2 * V &&
      // max_height is the upper bound
      (forall v :: (0 <= v < V && v!= s && v != t && excess[v] > 0) ==> height[v] <= max_height) &&
      // If a non terminal node is active it must be in the bucket of its current height
      (forall v :: (0 <= v < V && v != s && v != t && excess[v] > 0) ==> v in buckets[height[v]]) &&
      // If a node is in a bucket it must be active and cannot be a terminal node
      (forall h, v :: (0 <= h < 2 * V && 0 <= v < V && v in buckets[h]) ==> (excess[v] > 0 && v != s && v != t)) &&
      // If a node is in a bucket it must have the height of that bucket
      (forall h, v :: (0 <= h < 2 * V && 0 <= v < V && v in buckets[h]) ==> height[v] == h)
    }

    predicate ValidStructure()
      reads this
    {
      Graph.ValidGraph(V, s, t) &&
      FlowGraph.ValidFlowMatrixShape(V, flow) &&
      FlowGraph.ValidCapacityMatrixShape(V, capacity) &&
      FlowGraph.ValidHeightShape(V, height) &&
      FlowGraph.ValidExcessShape(V, excess) &&
      ValidBucketsStructure()
    }

    predicate Valid()
      reads this, capacity, flow, height, excess, buckets
    {
      ValidStructure() &&
      FlowGraph.ValidPreflow(V, s, t, capacity, flow) &&
      FlowGraph.ValidExcess(V, s, t, capacity, flow, excess) &&
      FlowGraph.ValidLabeling(V, s, t, capacity, flow, height) &&
      ValidBuckets()
    }

    function ResidualCapacity(v: nat, w: nat): nat
      reads this, capacity, flow
      requires Graph.ValidGraph(V, s, t)
      requires FlowGraph.ValidFlowMatrixShape(V, flow)
      requires FlowGraph.ValidCapacityMatrixShape(V, capacity)
      requires FlowGraph.ValidPreflow(V, s, t, capacity, flow)
      requires Graph.ValidNode(V, v) && Graph.ValidNode(V, w)
    {
      FlowGraph.ResidualCapacity(V, s, t, capacity, flow, v, w)
    }

    method Push(v: nat, w: nat)
      requires Valid()

      // Preconditions for a valid push:
      requires Graph.ValidNode(V, v) && Graph.ValidNode(V, w)   // v and w must be nodes in the Graph
      requires !FlowGraph.NodeIsSourceOrSink(v, s, t)           // v cannot be equal to the source or sink
      requires FlowGraph.NodeIsActive(V, v, excess)             // w must be active
      requires ResidualCapacity(v, w) > 0                       // There must be pipe space
      requires height[v] == height[w] + 1                       // Water must flow exactly one step downhill

      // postconditions
      ensures Valid()

      modifies flow, excess, buckets
    {
      // Calculate how much water we can push
      var delta := excess[v];
      var res_cap := ResidualCapacity(v, w);
      if (res_cap < delta) {
        delta := res_cap;
      }

      label BeforeMutation:
      flow[v, w] := flow[v, w] + delta;
      flow[w, v] := flow[w, v] - delta;
      FlowGraph.LemmaFlowSumAfterPush@BeforeMutation(V, flow, v, w, delta, V);

      // Store w's inital active state far later use
      var old_w_active := FlowGraph.NodeIsActive(V, w, excess);

      excess[v] := excess[v] - delta;
      excess[w] := excess[w] + delta;

      if (excess[v] == 0) {
        buckets[height[v]] := buckets[height[v]] - {v};
      }

      // Update the Highest-Label Buckets
      // If w was NOT active and w is not s or t, which implies it is active now, it enters the buckets.
      if (!old_w_active && !FlowGraph.NodeIsSourceOrSink(w, s, t)) {
        assert FlowGraph.NodeIsActive(V, w, excess);

        buckets[height[w]] := buckets[height[w]] + {w};
        // We don't need to update max_height here because water flows downhill
        // height[w] is strictly less than height[v], so it cannot become the new max_height.
      }
    }

    method Relabel(v: nat)
      requires Valid()

      // Preconditions for a valid relabel:
      requires Graph.ValidNode(V, v)                  // v must be a node in the Graph
      requires !FlowGraph.NodeIsSourceOrSink(v, s, t) // v cannot be equal to the source or sink
      requires FlowGraph.NodeIsActive(V, v, excess)   // v must be active
      // v cannot be relabeled if it has a downhill neighbor
      requires forall w :: 0 <= w < V && ResidualCapacity(v, w) > 0 ==> height[v] <= height[w]

      // Postconditions
      ensures Valid()

      modifies this, height, buckets
    {
      // Find the lowest neighbor in the residual graph
      // We initialize minHeightNeighbour to an impossibly high value (2 * V)
      var minHeightNeighbour: nat := 2 * V;
      var w := 0;
      while (w < V)
        invariant 0 <= w <= V
        invariant minHeightNeighbour <= 2 * V
        invariant forall k :: 0 <= k < w && ResidualCapacity(v, k) > 0 ==> minHeightNeighbour <= height[k]

        // Because v had no downhill neighbors, height[v] MUST be <= minHeightNeighbour.
        // invariant so that Dafny does not forget
        invariant height[v] <= minHeightNeighbour
      {
        if (ResidualCapacity(v, w) > 0) {
          if (height[w] < minHeightNeighbour) {
            minHeightNeighbour := height[w];
          }
        }
        w := w + 1;
      }
      // Assert minHeightNeighbour is actual minimum
      assert forall k :: 0 <= k < V && ResidualCapacity(v, k) > 0 ==> minHeightNeighbour <= height[k];

      // ------ Lemma's and proofs needed to prove height[v] < 2 * V after relabel ------
      // Prove a path to source exists from v
      FlowGraph.Lemma_ActiveVertexHasPathToSource(V, s, t, capacity, flow, excess, v);
      // Extract that path
      ghost var pathToSource :| FlowGraph.IsSimpleResidualPath(V, s, t, capacity, flow, pathToSource) && pathToSource[0] == v && pathToSource[|pathToSource|-1] == s;

      // Since v != s, the path has at least 2 nodes. Grab the next node in the path
      assert |pathToSource| >= 2;
      ghost var pathToSourceNextNode := pathToSource[1];

      // Because v and pathToSourceNextNode are connected on a residual path, there is residual capacity
      assert FlowGraph.ResidualCapacity(V, s, t, capacity, flow, v, pathToSourceNextNode) > 0;

      // get the remainder of the path (from pathToSourceNextNode to s)
      ghost var pathToSourceWithoutV := pathToSource[1..];

      // Apply length and telescoping height lemmas
      Graph.Lemma_SimplePathHasBoundedLength(V, pathToSource);
      assert |pathToSource| <= V;
      FlowGraph.Lemma_PathTelescopingHeight(V, s, t, capacity, flow, height, pathToSourceWithoutV);
      assert height[pathToSourceNextNode] <= height[s] + |pathToSourceWithoutV| - 1;
      assert height[pathToSourceNextNode] <= V + (V - 1) - 1; // Since height[s] == V && ((|pathToSource| <= V) ==> (|pathToSourceWithoutV| <= V - 1))
      assert height[pathToSourceNextNode] <= 2 * V - 2;
      assert height[pathToSourceNextNode] < 2 * V - 1;

      // This proves there exists a path to source where height[pathToSourceNextNode] < 2 * V - 1
      // minHeightNeighbour is the neighbour on the path where the next node has the minimum height
      // this means the following assertions also holds
      assert minHeightNeighbour < 2 * V - 1;
      assert minHeightNeighbour + 1 < 2 * V;
      // ------------

      buckets[height[v]] := buckets[height[v]] - {v};

      height[v] := minHeightNeighbour + 1;

      buckets[height[v]] := buckets[height[v]] + {v};

      if (height[v] > max_height) {
        max_height := height[v];
      }
    }
  }
}