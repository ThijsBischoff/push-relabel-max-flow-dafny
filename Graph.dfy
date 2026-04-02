module Graph {
  predicate ValidNode(V: nat, u: nat)
  {
    u < V
  }

  predicate NodeSequenceHasNoDuplicates(p: seq<nat>) {
    forall i, j :: 0 <= i < |p| && 0 <= j < |p| && i != j ==> p[i] != p[j]
  }

  predicate ValidGraph(V: nat, s: nat, t: nat)
  {
    V >= 2 &&
    ValidNode(V, s) && ValidNode(V, t) && s != t
  }

  lemma Lemma_SimplePathHasBoundedLength(V: nat, p: seq<nat>)
    requires NodeSequenceHasNoDuplicates(p)
    requires forall u :: 0 <= u < |p| ==> ValidNode(V, p[u])
    ensures |p| <= V
}