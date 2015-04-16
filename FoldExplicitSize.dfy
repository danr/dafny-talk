
datatype List<A> = Nil | Cons(A,List<A>)

function method Fold(xs : List<Expr>, unit : B, f : (Expr,B) -> B): B
  reads f.reads;
  requires forall x, y :: Size(x) < SizeL(xs) ==> f.requires(x,y);
{
  match xs
    case Nil => unit
    case Cons(x,xs) => f(x,SizeLemma(x,xs); Fold(xs,unit,f))
}

datatype Expr = Add(List<Expr>) | Mul(List<Expr>) | Lit(int)

function SizeL(e : List<Expr>): nat
{
  match e
    case Cons(e,es) => 1 + Size(e) + SizeL(es)
	case Nil        => 0
}

function Size(e : Expr): nat
{
  match e
    case Add(es) => 1 + SizeL(es)
    case Mul(es) => 1 + SizeL(es)
	case Lit(i)  => 0
}

lemma SizeLemma(e : Expr,es : List<Expr>)
  ensures SizeL(es) < SizeL(Cons(e,es))
{
}

function method Eval(ghost size: int, e : Expr): int
  requires size == Size(e)
  decreases size
{
  match e
    case Add(es) => Fold(es,0,(e',v) requires Size(e') < Size(e) => Eval(Size(e'),e') + v)
    case Mul(es) => Fold(es,1,(e',v) requires Size(e') < Size(e) => Eval(Size(e'),e') * v)
    case Lit(i)  => i
}

method Main() {
  var two := Lit(2);
  var add := (x,y) => Add(Cons(x,Cons(y,Nil)));
  assert Eval(Size(add(two,two)), add(two,two)) == 4;
}
