module Graph {
  predicate ValidNode(V: nat, u: nat)
  {
    u < V
  }

  predicate ValidEdge(V: nat, u: nat, v: nat)
  {
    u < V && v < V
  }
  
  predicate ValidCapacityShape(V: nat, capacity: array2<nat>)
  {
    capacity.Length0 == V && 
    capacity.Length1 == V
  }

  predicate ValidGraph(V: nat, s: nat, t: nat, capacity: array2<nat>)
    reads capacity
  {
    V >= 2 &&
    ValidNode(V, s) && ValidNode(V, t) && s != t &&
    ValidCapacityShape(V, capacity)
  }
}