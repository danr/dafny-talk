
class Ref<A> {
  var val: A;
}

method Test() {
  var g := () requires false => true;
  assert g.requires();
  assert !g.requires();
}

method Test2() {
  var g := () => true;
  assert g.requires();
  assert !g.requires();
}

method Landin() {
  var f : Ref<() -> bool>;

  f := new Ref;

  f.val := () reads f reads f.val.reads() requires !f.val.requires() => true;

  assert f.val.requires();
  assert f.val();
  assert !f.val.requires();
}

method Landin2() {
  var f : Ref<() -> bool>;

  f := new Ref;

  f.val := () reads f reads f.val.reads() requires  f.val.requires()
                                          requires !f.val.requires() => !f.val();

  assert f.val.requires();
  assert !f.val.requires();
  assert f.val();
  assert false;
}
