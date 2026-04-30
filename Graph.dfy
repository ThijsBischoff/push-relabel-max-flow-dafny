module Graph {
  type NodeCount = v: nat | v >= 2 witness 2
  const V: NodeCount

  type Node = n: nat | n < V witness 0
  type Path = p: seq<Node> | |p| > 0 witness [0]

  predicate IsSimplePath(p: Path) {
    forall i, j :: 0 <= i < |p| && 0 <= j < |p| && i != j ==> p[i] != p[j]
  }

  lemma Lemma_SimplePathHasBoundedLength(p: Path)
    requires IsSimplePath(p)
    ensures |p| <= V
}