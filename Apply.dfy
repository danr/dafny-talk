
function method Apply(f : A -> B, x : A): B
{
  f(x)
}

function method Compose(f :B ->C, g: A -> B, x: A): C
{
	f(g(x))
}
