

method Main() {

	var a := new int[10];

	var index : int -> int; // a could be in its reads clause!
							// index(x) could be a[x]

	assume index.requires(0);
	assume index(0) == 0;

	a[0] := 1;

    assert index.requires(0); // should not be provable 
	assert 0 == index(0);     // should not be provable!

}