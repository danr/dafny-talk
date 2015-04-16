
class Ref<A> {
  var val: A;
}

method Landin() {
  var f : Ref<() -> bool>;

  f := new Ref;

  f.val := () reads f reads f.val.reads () requires !f.val.requires() 
                                           requires  f.val.requires() => !f.val();

  if (f.val.requires()) {
	assert f.val();
  }
  assert false;
}

