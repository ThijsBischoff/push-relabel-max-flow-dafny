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

    var flow: array2<nat>
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
      (forall u :: (0 <= u < V && u != s && u != t && excess[u] > 0) ==>
                     height[u] <= max_height) &&
      (forall u :: (0 <= u < V && u != s && u != t && excess[u] > 0) ==>
                     u in buckets[height[u]]) &&
      (forall h, u :: (0 <= h < 2 * V && 0 <= u < V && u in buckets[h]) ==> height[u] == h)
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
      FlowGraph.ValidFlow(V, s, t, capacity, flow) &&
      FlowGraph.ValidPreflow(V, s, t, excess) &&
      FlowGraph.ValidLabeling(V, s, t, capacity, flow, height) &&
      ValidBuckets()
    }

    function ResidualCapacity(u: nat, v: nat): nat
      reads this, capacity, flow
      requires Graph.ValidGraph(V, s, t)
      requires FlowGraph.ValidFlowMatrixShape(V, flow)
      requires FlowGraph.ValidCapacityMatrixShape(V, capacity)
      requires FlowGraph.ValidFlow(V, s, t, capacity, flow)
      requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)
    {
      FlowGraph.ResidualCapacity(V, s, t, capacity, flow, u, v)
    }

    method Push(u: nat, v: nat)
      requires Valid()

      // Preconditions for a valid push:
      requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)   // u and v must be nodes in the Graph
      requires !FlowGraph.NodeIsSourceOrSink(u, s, t)           // u cannot be equal to the source or sink
      requires FlowGraph.NodeIsActive(V, u, excess)             // u must be active
      requires ResidualCapacity(u, v) > 0                       // There must be pipe space
      requires height[u] == height[v] + 1                       // Water must flow exactly one step downhill

      // postconditions
      ensures Valid()

      modifies flow, excess, buckets
    {
      // Calculate how much water we can push
      var push_val := excess[u];
      var res_cap := ResidualCapacity(u, v);
      if (res_cap < push_val) {
        push_val := res_cap;
      }

      // Cancel out any backward flow from v to u
      var cancel_flow := flow[v, u];
      if (push_val < cancel_flow) {
        cancel_flow := push_val;
      }
      flow[v, u] := flow[v, u] - cancel_flow;

      // Push the remaining amount forward from u to v
      var forward_push := push_val - cancel_flow;
      flow[u, v] := flow[u, v] + forward_push;

      // Store v's inital active state far later use
      var old_v_active := FlowGraph.NodeIsActive(V, v, excess);

      // Update the excess arrays
      excess[u] := excess[u] - push_val;
      excess[v] := excess[v] + push_val;

      // Update the Highest-Label Buckets
      // If v was NOT active, and is not s or t (which implies it is active now), it enters the buckets.
      if (!old_v_active && !FlowGraph.NodeIsSourceOrSink(v, s, t)) {
        assert FlowGraph.NodeIsActive(V, v, excess);

        buckets[height[v]] := buckets[height[v]] + {v};
        // We don't need to update max_height here because water flows downhill
        // height[v] is strictly less than height[u], so it cannot become the new max_height.
      }
    }

    method Relabel(u: nat)
      requires Valid()

      // Preconditions for a valid relabel:
      requires Graph.ValidNode(V, u)                  // u must be a node in the Graph
      requires !FlowGraph.NodeIsSourceOrSink(u, s, t) // u cannot be equal to the source or sink
      requires FlowGraph.NodeIsActive(V, u, excess)   // u must be active
      // u cannot be relabeled if it has a downhill neighbor
      requires forall v :: 0 <= v < V && ResidualCapacity(u, v) > 0 ==> height[u] <= height[v]

      // Postconditions
      ensures Valid()

      modifies this, height, buckets
    {
      // Find the lowest neighbor in the residual graph
      // We initialize minHeightNeighbourOfU to an impossibly high value (2 * V)
      var minHeightNeighbourOfU: nat := 2 * V;
      var v := 0;

      while (v < V)
        invariant 0 <= v <= V
        invariant minHeightNeighbourOfU <= 2 * V
        invariant forall k :: 0 <= k < v && ResidualCapacity(u, k) > 0 ==> minHeightNeighbourOfU <= height[k]

        // Because u had no downhill neighbors, height[u] MUST be <= minHeightNeighbourOfU.
        // invariant so that Dafny does not forget
        invariant height[u] <= minHeightNeighbourOfU
      {
        if (ResidualCapacity(u, v) > 0) {
          if (height[v] < minHeightNeighbourOfU) {
            minHeightNeighbourOfU := height[v];
          }
        }
        v := v + 1;
      }
      // Assert minHeightNeighbourOfU is actual minimum
      assert forall k :: 0 <= k < V && ResidualCapacity(u, k) > 0 ==> minHeightNeighbourOfU <= height[k];

      // Prove a path to the source exists from u
      FlowGraph.Lemma_ActiveNodeHasPathToSource(V, s, t, capacity, flow, excess, u);
      // Extract that path
      ghost var pathToSource :| FlowGraph.IsSimpleResidualPath(V, s, t, capacity, flow, pathToSource) && pathToSource[0] == u && pathToSource[|pathToSource|-1] == s;

      // Since u != s, the path has at least 2 nodes. Grab the next node in the path
      assert |pathToSource| >= 2;
      ghost var pathToSourceNextNode := pathToSource[1];

      // Because u and path_v are connected on a residual path, there is residual capacity
      assert FlowGraph.ResidualCapacity(V, s, t, capacity, flow, u, pathToSourceNextNode) > 0;

      // get the remainder of the path (from path_v to s)
      ghost var pathToSourceWithoutU := pathToSource[1..];

      // Apply length and telescoping height lemmas
      Graph.Lemma_SimplePathHasBoundedLength(V, pathToSource);
      assert |pathToSource| <= V;
      FlowGraph.Lemma_PathTelescopingHeight(V, s, t, capacity, flow, height, pathToSourceWithoutU);
      assert height[pathToSourceNextNode] <= height[s] + |pathToSourceWithoutU| - 1;
      // Since |pathToSource| <= V, the subpath has length <= V - 1
      assert |pathToSourceWithoutU| <= V - 1;
      // Since height[s] == V, we get:
      assert height[pathToSourceNextNode] <= V + (V - 1) - 1;
      assert height[pathToSourceNextNode] <= 2 * V - 2;
      assert height[pathToSourceNextNode] < 2 * V - 1;

      // This proves there exists a path to source where
      // - height[pathToSourceNextNode] < 2 * V - 1
      // minHeightNeighbourOfU is the neighbour on the path where the next node has the minimum height
      // this means the following assertion also holds
      assert minHeightNeighbourOfU < 2 * V - 1;

      // Remove u from its old bucket
      buckets[height[u]] := buckets[height[u]] - {u};

      // Update u's height
      height[u] := minHeightNeighbourOfU + 1;
      // from these above lemmas we can thus conclude that height[u] falls within the bounds of the buckets
      assert height[u] < 2 * V;

      // Add u to its new, higher bucket
      buckets[height[u]] := buckets[height[u]] + {u};

      // Because we lifted a node, it might be the new absolute highest active node
      if (height[u] > max_height) {
        max_height := height[u];
      }
    }
  }
}