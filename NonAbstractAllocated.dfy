

method Main() {

	var a := new int[10];

	var index := i reads a requires 0 <= i < 10 => a[i]; 
					

	assume index.requires(0);
	assume index(0) == 0;

	a[0] := 1;

    assert index.requires(0); 
	assert 0 == index(0);     // should not be provable!

}