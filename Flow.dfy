include "Graph.dfy"

module FlowGraph {
  import opened Graph

  type Capacity = c: seq<seq<nat>> | |c| == V && forall i :: 0 <= i < |c| ==> |c[i]| == V witness seq(V, _ => seq(V, _ => 0))
  type Flow = f: seq<seq<int>> | |f| == V && forall i :: 0 <= i < |f| ==> |f[i]| == V witness seq(V, _ => seq(V, _ => 0))

  function ResidualCapacity(c: Capacity, f: Flow, v: Node, w: Node): nat
    requires ValidCapacityConstraint(c, f)
  {
    c[v][w] - f[v][w]
  }

  // Computes the sum of flow into node 'v' on edges from (0, v) up to edge ('maxSource', v)
  function SumTotalFlowToNode(f: Flow, v: Node, maxSource: nat): int
    requires maxSource < V
    decreases maxSource
  {
    if maxSource == 0 then
      f[0][v]
    else
      f[maxSource][v] + SumTotalFlowToNode(f, v, maxSource-1)
  }

  function SumFlowFromSetToNode(f: Flow, S: set<Node>, v: Node, maxSource: nat): int
    requires maxSource < V
    decreases maxSource
  {
    (if maxSource in S then f[maxSource][v] else 0) +
    (if maxSource == 0 then 0 else SumFlowFromSetToNode(f, S, v, maxSource - 1))
  }

  function SumFlowFromNodeToSet(f: Flow, S: set<Node>, v: Node, maxDest: nat): int
    requires maxDest < V
    decreases maxDest
  {
    (if maxDest in S then f[v][maxDest] else 0) +
    (if maxDest == 0 then 0 else SumFlowFromNodeToSet(f, S, v, maxDest - 1))
  }

  function SumFlowFromAllNodesToSet(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat): int
    requires maxSource < V && maxDest < V
    decreases maxSource
  {
    SumFlowFromNodeToSet(f, S, maxSource, maxDest) +
    (if maxSource == 0 then 0 else SumFlowFromAllNodesToSet(f, S, maxSource - 1, maxDest))
  }

  function SumIncomingFlowOfSet(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat): int
    requires maxSource < V && maxDest < V
    decreases maxDest
  {
    (if maxDest in S then SumTotalFlowToNode(f, maxDest, maxSource) else 0) +
    (if maxDest == 0 then 0 else SumIncomingFlowOfSet(f, S, maxSource, maxDest - 1))
  }

  function SumInternalFlowToSet(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat): int
    requires maxSource < V && maxDest < V decreases maxSource
  {
    (if maxSource in S then SumFlowFromNodeToSet(f, S, maxSource, maxDest) else 0) +
    (if maxSource == 0 then 0 else SumInternalFlowToSet(f, S, maxSource - 1, maxDest))
  }

  function SumExternalFlowToSet(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat): int
    requires maxSource < V && maxDest < V
    decreases maxSource
  {
    (if maxSource !in S then SumFlowFromNodeToSet(f, S, maxSource, maxDest) else 0) +
    (if maxSource == 0 then 0 else SumExternalFlowToSet(f, S, maxSource - 1, maxDest))
  }

  ghost function NodesReachableFrom(c: Capacity, f: Flow, v: Node): set<Node>
    requires ValidCapacityConstraint(c, f)
  {
    set w: Node | exists p: Path :: IsSimpleResidualPath(c, f, p) && p[0] == v && p[|p|-1] == w
  }

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
    forall v: Node {:trigger SumTotalFlowToNode(f, v, V - 1)} | (v != s && v != t) :: (SumTotalFlowToNode(f, v, V - 1) == 0)
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
  
  lemma Lemma_ZeroFlowEqualsZeroSumFlowInOfNode(f: Flow, v: Node, u: nat)
    requires u < V
    requires forall i: Node, j: Node :: f[i][j] == 0
    ensures SumTotalFlowToNode(f, v, u) == 0
  {
    // automatically verified by Dafny
  }

  lemma Lemma_NodeReachableFromReachableSetIsReachable(c: Capacity, f: Flow, v: Node, n: Node, m: Node)
    requires ValidCapacityConstraint(c, f)
    requires n in NodesReachableFrom(c, f, v)
    requires ResidualCapacity(c, f, n, m) > 0
    ensures m in NodesReachableFrom(c, f, v)
  {
    var p :| IsSimpleResidualPath(c, f, p) && p[0] == v && p[|p|-1] == n;
    if m in p {
      var k :| 0 <= k < |p| && p[k] == m;
      assert IsSimpleResidualPath(c, f, p[..k+1]);
    } else {
      assert IsSimpleResidualPath(c, f, p + [m]);
    }
  }

  lemma Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Base(f: Flow, S: set<Node>, maxDest: nat)
    requires maxDest < V
    ensures SumIncomingFlowOfSet(f, S, 0, maxDest) == SumFlowFromNodeToSet(f, S, 0, maxDest)
    decreases maxDest
  {
    if maxDest > 0 { Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Base(f, S, maxDest - 1); }
    // intuition: Sum of incomming flow into the first node of the set is equal to flow from all nodes to the first node of the set.
  }

  lemma Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Step(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat)
    requires maxSource < V && maxDest < V && maxSource > 0
    ensures SumIncomingFlowOfSet(f, S, maxSource, maxDest) == SumFlowFromNodeToSet(f, S, maxSource, maxDest) + SumIncomingFlowOfSet(f, S, maxSource - 1, maxDest)
    decreases maxDest
  {
    if maxDest > 0 { Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Step(f, S, maxSource, maxDest - 1); }
    // intuition: Sum of incomming flow into set from maxSource to maxDestination
    // is equal to the sum of incoming flow into set from maxSource - 1 to maxDestination + the flow from maxSource to maxDestination.
  }

  lemma Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat)
    requires maxSource < V && maxDest < V
    ensures SumIncomingFlowOfSet(f, S, maxSource, maxDest) == SumFlowFromAllNodesToSet(f, S, maxSource, maxDest)
    decreases maxSource
  {
    if maxSource == 0 {
      Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Base(f, S, maxDest);
    } else {
      Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet(f, S, maxSource - 1, maxDest);
      Lemma_SumIncomingFlowOfSetEqualsSumFlowFromAllNodesToSet_Step(f, S, maxSource, maxDest);
    }
  }

  lemma Lemma_NodeInternalFlowCancelsOut(f: Flow, S: set<Node>, v: Node, limit: nat)
    requires limit < V
    requires ValidSkewSymmetryConstraint(f)
    ensures SumFlowFromNodeToSet(f, S, v, limit) + SumFlowFromSetToNode(f, S, v, limit) == 0
    decreases limit
  {
    if limit > 0 { Lemma_NodeInternalFlowCancelsOut(f, S, v, limit - 1); }
    // intuition: Because of skew symmetry this holds, f[v][w] = -f[w][v]
  }

  lemma Lemma_InternalFlowStep(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat)
    requires maxDest < V && maxSource < V
    requires maxDest > 0 && maxSource < maxDest
    ensures SumInternalFlowToSet(f, S, maxSource, maxDest) ==
            SumInternalFlowToSet(f, S, maxSource, maxDest - 1) + (if maxDest in S then SumFlowFromSetToNode(f, S, maxDest, maxSource) else 0)
    decreases maxSource
  {
    if maxSource > 0 { Lemma_InternalFlowStep(f, S, maxSource - 1, maxDest); }
    // intuition: Sum of internal flow in set limited by maxSource and maxDest
    // = sum of internal flow in set limited by maxSource and maxDest - 1
    // + internal flow to maxDest limited by maxSource if maxDest is in the set
  }

  lemma Lemma_TotalInternalFlowOfSetIsZero(f: Flow, S: set<Node>, limit: nat)
    requires limit < V
    requires ValidSkewSymmetryConstraint(f)
    ensures SumInternalFlowToSet(f, S, limit, limit) == 0
    decreases limit
  {
    if limit > 0 {
      Lemma_TotalInternalFlowOfSetIsZero(f, S, limit - 1);
      Lemma_InternalFlowStep(f, S, limit - 1, limit);

      if limit in S { Lemma_NodeInternalFlowCancelsOut(f, S, limit, limit); }

      // Follows from Lemma_InternalFlowStep
      assert SumInternalFlowToSet(f, S, limit, limit) ==
            // shown to be 0 by induction
            SumInternalFlowToSet(f, S, limit - 1, limit - 1)
            // shown to be 0 by Lemma_NodeInternalFlowCancelsOut
            + (if limit in S then SumFlowFromSetToNode(f, S, limit, limit) + SumFlowFromNodeToSet(f, S, limit, limit) else 0)
            // postcondition
            == 0;
    }
  }

  lemma Lemma_SumFlowFromAllNodesEqualsSumInternalFlowPlusSumExternalFlow(f: Flow, S: set<Node>, maxSource: nat, maxDest: nat)
    requires maxSource < V && maxDest < V
    ensures SumFlowFromAllNodesToSet(f, S, maxSource, maxDest) == SumInternalFlowToSet(f, S, maxSource, maxDest) + SumExternalFlowToSet(f, S, maxSource, maxDest)
    decreases maxSource
  {
    if maxSource > 0 { Lemma_SumFlowFromAllNodesEqualsSumInternalFlowPlusSumExternalFlow(f, S, maxSource - 1, maxDest); }
    // intuition: Sum of flow from all nodes to set
    // equals sum of from from nodes outside of set to set + sum of flow from nodes inside of set to set.
  }

  lemma Lemma_FlowFromExternalNodeToReachableSetIsNonPositive(c: Capacity, f: Flow, v: Node, S: set<Node>, extNode: Node, limit: nat)
    requires ValidCapacityConstraint(c, f) && ValidSkewSymmetryConstraint(f)
    requires S == NodesReachableFrom(c, f, v)
    requires extNode !in S
    requires limit < V
    ensures SumFlowFromNodeToSet(f, S, extNode, limit) <= 0
    decreases limit
  {
    // show postcondition holds for set up to and including limit - 1
    if limit > 0 { Lemma_FlowFromExternalNodeToReachableSetIsNonPositive(c, f, v, S, extNode, limit - 1); }

    // SumFlowFromNodeToSet only changes if limit is in S
    if limit in S {
      // prove residual capacity is 0 by contradiction
      assert ResidualCapacity(c, f, limit, extNode) == 0 by {
        if ResidualCapacity(c, f, limit, extNode) > 0 {
          assert extNode in S by {
            Lemma_NodeReachableFromReachableSetIsReachable(c, f, v, limit, extNode);
          }
          assert false;
        }
      }

      assert 0 <= c[limit][extNode] == f[limit][extNode]; // by ValidCapacityConstraint and residual capacity of 0
      assert f[limit][extNode] == -f[extNode][limit]; // by ValidSkewSymmetryConstraint
      assert f[extNode][limit] <= 0; // follows from above assertions

      assert SumFlowFromNodeToSet(f, S, extNode, limit) == 
       (if limit > 0 then SumFlowFromNodeToSet(f, S, extNode, limit - 1) else 0) // <= 0 by induction
       + (if limit in S then f[extNode][limit] else 0); // <= 0 by inductive step
    }
  }

  lemma Lemma_TotalExternalFlowOfReachableSetIsNonPositive(c: Capacity, f: Flow, v: Node, S: set<Node>, maxSource: nat, maxDest: nat)
    requires ValidCapacityConstraint(c, f) && ValidSkewSymmetryConstraint(f)
    requires S == NodesReachableFrom(c, f, v)
    requires maxSource < V && maxDest < V
    ensures SumExternalFlowToSet(f, S, maxSource, maxDest) <= 0
    decreases maxSource
  {
    // show postcondition holds for set up to and including maxSource - 1
    if maxSource > 0 { Lemma_TotalExternalFlowOfReachableSetIsNonPositive(c, f, v, S, maxSource - 1, maxDest); }
    // show that it holds for maxSource
    if maxSource !in S { Lemma_FlowFromExternalNodeToReachableSetIsNonPositive(c, f, v, S, maxSource, maxDest); }
  }
}