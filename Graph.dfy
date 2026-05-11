module Graph {
  type NodeCount = v: nat | v >= 2 witness 2
  const V: NodeCount

  type Node = n: nat | n < V witness 0
  type Path = p: seq<Node> | |p| > 0 witness [0]

  predicate IsSimplePath(p: Path) {
    forall i, j :: 0 <= i < |p| && 0 <= j < |p| && i != j ==> p[i] != p[j]
  }

  lemma Lemma_SimplePathHasBoundedLength(p: Path, bound: nat)
    requires bound <= V // requires bound to be less than nodeCount
    requires IsSimplePath(p)
    requires forall i :: 0 <= i < |p| ==> p[i] < bound // requires all elements to be less than bound

    ensures |p| <= bound

    decreases bound
  {
    if |p| == 1 {
      // automatically verified by Dafny
    } else {
      assert bound > 1 by {
        assert bound >= 0; // since it is a nat
        if bound == 0 {
          assert |p| > 1;
          assert p[0] < bound;
          assert false; // since nodes cannot be less than 0 (Node is subtype of nat)
        } else if bound == 1 {
          assert bound == 1;
          assert p[0] == p[1];
          assert false; // sinc nodes cannot be the same (simple path)
        }
        assert bound > 1;
      }

      var maxElem := (bound - 1) as Node; // The maximum possible value in the sequence
      if maxElem in p {
        var idx :| 0 <= idx < |p| && p[idx] == maxElem; // get the max value's index
        var p' := p[..idx] + p[idx+1..]; // remove the max value from the sequence

        // p' is still a sequence without duplicates
        // bounded by bound - 1 since the element bound - 1 is removed
        Lemma_SimplePathHasBoundedLength(p', bound - 1);
      } else {
        // all elements are already strictly < bound - 1
        Lemma_SimplePathHasBoundedLength(p, bound - 1);
      }
    }
  }
}