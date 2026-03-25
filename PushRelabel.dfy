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

    var buckets: array<seq<nat>>
    var max_height: int

    predicate NodeIsSourceOrSink(u: nat)
      reads this
    {
      u == s || u == t
    }

    predicate ValidBucketsStructure()
      reads this, buckets
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
      (forall u :: 0 <= u < V && u != s && u != t && excess[u] > 0 ==>
                     height[u] <= max_height) &&
      (forall u :: 0 <= u < V && u != s && u != t && excess[u] > 0 ==>
                     u in buckets[height[u]])
    }

    predicate ValidStructure()
      reads this, capacity, flow, height, excess, buckets
    {
      Graph.ValidGraph(V, s, t, capacity) &&
      FlowGraph.ValidFlowMatrixShape(V, flow) &&
      FlowGraph.ValidHeightShape(V, height) &&
      FlowGraph.ValidExcessShape(V, excess) &&
      ValidBucketsStructure()
    }

    predicate Valid()
      reads this, capacity, flow, height, excess, buckets
    {
      ValidStructure() &&
      FlowGraph.ValidFlow(V, s, t, capacity, flow) &&
      FlowGraph.ValidPreflow(V, s, t, capacity, excess) &&
      FlowGraph.ValidLabeling(V, s, t, capacity, flow, height) &&
      ValidBuckets()
    }

    function ResidualCapacity(u: nat, v: nat): nat
      reads this, capacity, flow
      requires Graph.ValidGraph(V, s, t, capacity)
      requires FlowGraph.ValidFlowMatrixShape(V, flow)
      requires FlowGraph.ValidFlow(V, s, t, capacity, flow)
      requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)
    {
      FlowGraph.ResidualCapacity(V, s, t, capacity, flow, u, v)
    }

    method Push(u: nat, v: nat)
      requires Valid()

      // Preconditions for a valid push:
      requires Graph.ValidNode(V, u) && Graph.ValidNode(V, v)   // u and v must be nodes in the Graph
      requires !NodeIsSourceOrSink(u)                           // u cannot be equal to the source or sink
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
      // If v was NOT active, and is not s or t (which implies it is active), it enters the buckets.
      if (!old_v_active && !NodeIsSourceOrSink(v)) {
        assert FlowGraph.NodeIsActive(V, v, excess);

        buckets[height[v]] := buckets[height[v]] + [v];
        // We don't need to update max_height here because water flows downhill!
        // height[v] is strictly less than height[u], so it cannot become the new max_height.
      }
    }

    method Relabel(u: nat)
      requires Valid()

      // Preconditions for a valid relabel:
      requires Graph.ValidNode(V, u)                  // u must be a node in the Graph
      requires !NodeIsSourceOrSink(u)                 // u cannot be equal to the source or sink
      requires FlowGraph.NodeIsActive(V, u, excess)   // u must be active
      // u cannot be relabeled if it has a downhill neighbor
      requires forall v :: 0 <= v < V && ResidualCapacity(u, v) > 0 ==> height[u] <= height[v]

      // Postconditions
      ensures Valid()

      modifies this, height, buckets
    {
      // Find the lowest neighbor in the residual graph
      // We initialize min_h to an impossibly high value (2 * V)
      var min_h: nat := 2 * V;
      var v := 0;

      while (v < V)
        invariant 0 <= v <= V
        invariant min_h <= 2 * V
        // Loop invariant needed here to prove we find the actual minimum
        invariant forall k :: 0 <= k < v && ResidualCapacity(u, k) > 0 ==> min_h <= height[k]

        // Because u had no downhill neighbors, height[u] MUST be <= min_h.
        // invariant so that Dafny does not forget
        invariant height[u] <= min_h
      {
        if (ResidualCapacity(u, v) > 0) {
          if (height[v] < min_h) {
            min_h := height[v];
          }
        }
        v := v + 1;
      }
      // Assert min_h is actual minimum
      assert forall k :: 0 <= k < V && ResidualCapacity(u, k) > 0 ==> min_h <= height[k];

      // (TODO: Lemma to prove this is correct)
      assume min_h < 2 * V - 1;

      height[u] := min_h + 1;

      // Update the Highest-Label Buckets
      // Add the node to its new, higher bucket (Stale Entry strategy: we don't remove the old one)
      buckets[height[u]] := buckets[height[u]] + [u];

      // Because we lifted a node, it might be the new absolute highest active node
      if (height[u] > max_height) {
        max_height := height[u];
      }
    }
  }
}