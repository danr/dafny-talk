
method ArrayMap(a : array<A>, f : (int,A) -> A)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j,a[j])
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j,a[j])
  modifies a 
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j,old(a[j]))
{
  var N := a.Length;
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N;
    invariant forall j :: 0 <= j < i ==> a[j] == f(j,old(a[j]))
	invariant forall j :: i <= j < N ==> a[j] == old(a[j])
  {
    a[i] := f(i,a[i]);
    i := i + 1;
  }
}

/*
method Main() 
{
  var v := new int[10];
  ArrayMap(v, (i,_) => i);
  PrintArray(v);
  ArrayMap(v, (_,x) => x + 1);
  PrintArray(v);
  ArrayMap(v, (_,x) requires x != 0 => 100 / x);
  PrintArray(v);
  var u := new int[10];
  ArrayMap(u, (i,_) requires 0 <= i < 10 reads v => v[i]);
  PrintArray(u);
  var z := new int[9];
  ArrayMap(z, (i,_) requires 0 <= i < 9 reads u => u[i] + u[i+1]);
  PrintArray(z);
  assert z[8] == 21; 
}
*/

method PrintArray(a : array<int>)
  requires a != null;
{
  var i := 0;
  while (i < a.Length) {
    if (i != 0) {
	  print ", ";
	}
    print a[i];
    i := i + 1;
  }
  print "\n";
}
