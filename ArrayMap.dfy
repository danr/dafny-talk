
method ArrayMap(a : array<A>, f : (int,A) -> A)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> true 
  requires forall j :: 0 <= j < a.Length ==> true 
  modifies a 
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j,old(a[j]))
{
  var N := a.Length;
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> true 
    invariant forall j :: i <= j < N ==> true 
    invariant 0 <= i <= N;
  {
    a[i] := f(i,a[i]);
    i := i + 1;
  }
}

/*
method Main() 
{
  var v := new int[10];
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

/*
  requires forall j :: 0 <= j < a.Length ==> f.requires(j,a[j])
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j,a[j])

    invariant forall j :: 0 <= j < i ==> a[j] == f(j,old(a[j]))
    invariant forall j :: i <= j < N ==> a[j] == old(a[j])
*/