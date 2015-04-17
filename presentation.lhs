\documentclass[ignorenonframetext,]{beamer}

%include polycode.fmt

%format bun    = "\begin{uncoverenv}<2-> "
%format unb    = "\end{uncoverenv} "
%format FrameF = "\mathit{Frame_F}"
%format alpha  = "\alpha"
%format h1
%format h2
%format ==>    = "\Longrightarrow"
%format forall = "\forall"
%format zo'u   = "."
%format /=     = "\neq"
%format ==     = "="
%format !=     = "\neq"
%format quad   = "\quad\quad"

%format assert   = "\mathbf{assert}"
%format reads    = "\mathbf{reads}"
%format requires = "\mathbf{requires}"
%format havoc    = "\mathbf{havoc}"
%format assume   = "\mathbf{assume}"

%format xbar   = "\overline{x}"

%format e1
%format e2

%format x3
%format an     = "\mathit{a_n}"

%format tr a = "\llbracket " a "\rrbracket "
%format (tr (a)) = "\llbracket " a "\rrbracket "

\setbeamertemplate{caption}[numbered]
\setbeamertemplate{caption label separator}{:}
\setbeamercolor{caption name}{fg=normal text.fg}
\usepackage{helvet}
\usepackage{amssymb,amsmath}
\usepackage{ifxetex,ifluatex}
\usepackage{fixltx2e} % provides \textsubscript
\usepackage{lmodern}
\usepackage{inconsolata}
\ifxetex
  \usepackage{fontspec,xltxtra,xunicode}
  \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
  \newcommand{\euro}{€}
\else
  \ifluatex
    \usepackage{fontspec}
    \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
    \newcommand{\euro}{€}
  \else
    \usepackage[T1]{fontenc}
    \usepackage[utf8]{inputenc}
      \fi
\fi
% use upquote if available, for straight quotes in verbatim environments
\IfFileExists{upquote.sty}{\usepackage{upquote}}{}
% use microtype if available
\IfFileExists{microtype.sty}{\usepackage{microtype}}{}

% Comment these out if you don't want a slide with just the
% part/section/subsection/subsubsection title:
\AtBeginPart{
  \let\insertpartnumber\relax
  \let\partname\relax
  \frame{\partpage}
}
\AtBeginSection{
  \let\insertsectionnumber\relax
  \let\sectionname\relax
  \frame{\sectionpage}
}
\AtBeginSubsection{
  \let\insertsubsectionnumber\relax
  \let\subsectionname\relax
  \frame{\subsectionpage}
}

\newcommand{\vp}{\pause{\vspace{-2\baselineskip}}}

\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 2pt minus 1pt}
\setlength{\emergencystretch}{3em}  % prevent overfull showes
\setcounter{secnumdepth}{0}

% Abstract
%
% Work in progress on fit HOFs/first-class-functions to the verification system
% Dafny.

\title{First-class functions in Dafny}
%\subtitle{... or what I did last summer}
\institute{}

\author{Dan Ros\'en \\ \vspace{\baselineskip} with Rustan Leino}
\date{} % June 4, 2013}

\begin{document}

\begin{frame}
\maketitle
\end{frame}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{frame}[fragile]{Dafny}

\begin{itemize}
\item Imperative and OO verifier
\item Supports (co-) data types
\item Built in types for sets, maps, sequences, etc
\item No higher-order-functions, until now
\end{itemize}

\end{frame}

% First some simple thing

% Then, array map and show some loop invariants

% Then talk a bit about the frame axiom

\begin{frame}[fragile]{Well-formedness check}
\begin{center}
Dafny $\rightarrow$ Boogie $\rightarrow$ Z3
\end{center}

> WF : Dafny.Expr -> Boogie.Stmt
> WF ( e1 / e2 ) = WF ( e1 ) ; WF ( e2 ) ; assert (tr e2) != 0 ; {-"\uncover<2->{"-}
> WF ( \ x reads a requires b => c ) =
>     WF ( a );
>     WF ( b );
>     if * {
>         OldHeap := Heap;
>         havoc Heap;
>         assume HeapSucc(OldHeap, Heap);
>         assume (tr b);
>         WF ( c );
>         assume false;
>     } {-"}"-}


\end{frame}

\begin{frame}[fragile]{Well-formedness of expression application}
> WF : Dafny.Expr -> Boogie.Stmt
> WF ( e x ) =
>     WF ( e ) ;
>     WF ( x ) ;
>     assert Requires(Heap, tr e,tr x);
> {-"\uncover<2->{"-}
> tr : Dafny.Expr -> Boogie.Expr
> tr ( e x ) = Apply(Heap, tr e,tr x)
> tr ( \ x reads a requires b => c ) = ? {-"}"-}
\end{frame}

\begin{frame}[fragile]{Lambdas in Boogie}

\begin{verbatim}
    var f : [int]int;
    var j : int;
    f := (lambda x :: x + j);
    assert f[0] == j;
\end{verbatim}

\pause
Removed by defunctionalization:

\begin{verbatim}
function apply<a,b>(closure a b, a): b;
function f_closure(int): closure int int;
axiom (forall x,j : int :: apply(f_closure(j),x) = x+j);
\end{verbatim}

\begin{verbatim}
    var f : closure int int;
    var j : int;
    f := f_closure(j);
    assert apply(f,0) == j;
\end{verbatim}

\end{frame}

\begin{frame}[fragile]{Lambda functions in Dafny}

> tr : Dafny.Expr -> Boogie.Expr
> tr ( \ x reads a requires b => c ) = ?
\pause

\begin{verbatim}
var f := x reads a requires x != 0 => a[0] + 100 / x;
\end{verbatim}

\pause

Translates to a triple record:

\begin{verbatim}
Handle([heap,int]int, [heap,int]bool, [heap,int]set)

    f := Handle((lambda h, x :: h[a,Ix(0)] + 100 / x),
                (lambda h, x :: x != 0),
                (lambda h, x :: Singleton(a)))
\end{verbatim}

\pause

\begin{verbatim}
function Apply(heap,Handle,int): int;
(forall f,req,read,h,x ::
        Apply(h,Handle(f,req,read),x) = f[h,x])
\end{verbatim}
\end{frame}


\begin{frame}[fragile]{The heap in Dafny}

Using a polymorphic lambda:

\begin{verbatim}
type Heap = <a>[ref, Field a]a

function Ix(int) : Field int;

\end{verbatim}

Dafny:   @a[0]@

Boogie:  @h[a,Ix(0)]@

\end{frame}


\begin{frame}[fragile]{The frame axiom}

One copy for each concrete function $F$ and its frame |FrameF|:

> forall h1 h2 xbar zo'u  (forall alpha, o : ref, f : Field alpha zo'u
>                               o `elem` FrameF ==> h1[o,f] = h2[o,f])
>                         ==>   F(h1,xbar) = F(h2,xbar)

Why:
\begin{itemize}
\item For recursive functions
\item The function is abstract (in another module, or a stub)
\item Similarily, the function could now be a parameter
\end{itemize}

\end{frame}

\begin{frame}[fragile]{The frame for abstract functions}

> forall H h1 h2 xbar zo'u  (forall alpha, o : ref, f : Field alpha zo'u
>                            o `elem` Reads(H,h1,xbar) ==> h1[o,f] = h2[o,f])
>                           ==>   Apply(h1,H,xbar) = Apply(h2,H,xbar)
\pause
> forall H h1 h2 xbar zo'u  (forall alpha, o : ref, f : Field alpha zo'u
>                                 o `elem` Reads(H,h1,xbar) ==> h1[o,f] = h2[o,f])
>                           ==>   Requires(h1,H,xbar) = Requires(h2,H,xbar)

\end{frame}

\begin{frame}[fragile]{Termination of partial functions}

% demo fold map + maybe show some example of nontermination

% In Dafny, each function has a decreases clause (sometimes implicit)

% decreases clause

% turns out to be quite easy (in practice)

% in theory: how can we prove this to be correct?

Conjectures about ``Functional'' (heap-less) Dafny:

\begin{itemize}
\item First-order programs terminate
\item Higher-order programs terminate
\end{itemize}

\end{frame}

\begin{frame}[fragile]{Landin knots}

% normal knots are ok since of the requires.
%
% requires-knots are ok since below
%
% read-knots?
%
%
% rationale:
%
% cannot case on !g.requires()
%
% why:
%
% operationally: the compiler is free to implement a function that crashes less often
\begin{verbatim}
function Apply(Handle,heap,int): int;

(forall f,req,read,h,x ::
        Apply(Handle(f,req,read),h,x) = f[h,x])
\end{verbatim}\pause
\begin{verbatim}
function Requires(Handle,heap,int): bool;

(forall f,req,read,h,x ::
        req[h,x] ==> Requires(Handle(f,req,read),h,x)
\end{verbatim}


\end{frame}

\begin{frame}[fragile]{Conclusion}

\begin{itemize}
\item Adding HOFs not trivial
\item Callbacks work well
\item Partial functions for termination
\item \verb~http://rise4fun.com/Dafny~
\end{itemize}

\end{frame}

\begin{frame}[fragile]{Exponential datatypes}

> datatype D = K(D -> D)

Now, |D| is inhabited:

> var d : D = K(x requires false => botelim())

\end{frame}


\begin{frame}[fragile]{}



\end{frame}

\end{document}
