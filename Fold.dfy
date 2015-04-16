
datatype List<A> = Nil | Cons(A,List<A>)

function method Fold(xs : List<A>, unit : B, f : (A,B) -> B): B
  reads f.reads;
  requires forall x, y :: x < xs ==> f.requires(x,y);
{
  match xs
    case Nil => unit
    case Cons(x,xs) => f(x,Fold(xs,unit,f))
}

datatype Expr = Add(List<Expr>) | Mul(List<Expr>) | Lit(int)

function method Eval(e : Expr): int
{
  match e
    case Add(es) => Fold(es,0,(e,v) requires e < es => Eval(e) + v)
    case Mul(es) => Fold(es,1,(e,v) requires e < es => Eval(e) * v)
    case Lit(i)  => i
}

method Main() {
  var two := Lit(2);
  var add := (x,y) => Add(Cons(x,Cons(y,Nil)));
  assert Eval(add(two,two)) == 4;
}
