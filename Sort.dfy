datatype List<A> = Nil | Cons(A,List<A>)

function Length(xs : List<A>) : nat
{
  match xs
    case Nil => 0
	case Cons(x,xs) => 1 + Length(xs)
}

function Append(xs : List<A>, ys : List<A>) : List<A>
{
  match xs 
    case Nil => Nil
	case Cons(x,xs) => Cons(x,Append(xs,ys))
}

function Filter(xs : List<A>, p : A -> bool) : List<A>
  reads p.reads
  requires forall a :: p.requires(a)
  // ensures Length(Filter(xs,p)) <= Length(xs)
{
  match xs 
    case Nil => Nil
	case Cons(x,xs) => if p(x) then Cons(x,Filter(xs,p)) else Filter(xs,p)
}

function QSort(cmp : (A,A) -> bool, xs : List<A>) : List<A>
  reads cmp.reads
  requires forall x,y :: cmp.requires(x,y)
  decreases Length(xs)
{
  match xs
	case Nil => Nil
	case Cons(p,xs) => Append(QSort(cmp,Filter(xs,x reads cmp.reads(x,p) requires cmp.requires(x,p) => cmp(x,p))),
 	  			       Cons(p,QSort(cmp,Filter(xs,x reads cmp.reads(p,x) requires cmp.requires(p,x) => cmp(p,x))))) 
}
