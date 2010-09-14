<TeXmacs|1.0.7.3>

<style|article>

<\body>
  <assign|cov|<macro|<math|\<vartriangleleft\>>>>

  <doc-data|<doc-title|Lagrange polynomials and non-trivial spaces of
  zeros>|<doc-author-data|<author-name|Bas Spitters>>>

  <\abstract>
    The correctness of the error term for Lagrange interpolation is one of
    the basic results in numerical integration and differentiation. Bishop
    proposed to use constructive mathematics as a programming language for
    numerical analysis. Hence, to advance this program, it is important to
    obtain a smooth constructive proof of this fact. Here we provide three
    such proofs: an approximate version, a constructive interpretation of the
    classical proof using formal topology, and an informative proof using the
    Hermite-Genocchi formula.
  </abstract>

  <section|Introduction>

  Rolle's theorem is a key method in numerical analysis. Hence it is
  fundamental to study its formalization in type theory. Since the double
  negation of the axiom of countable choice is not constructively provable.
  Hence a simple use of the double negation monad does not seem to be enough.
  In Section<nbsp><reference|generic>, we present an alternative method to
  interpret classical proofs: sheaf models (see also Coquand). As usual, an
  approximate version is also available, but seems more elaborate than the
  classical proof. Finally, the use of divided differences gives a satisfying
  constructive account which is arguably superior to the classical
  development.

  \;

  TODO:

  Bishop, formal topology, sheaf models, geometric logic. Palmgren embedding.
  Intermediate value theorem.

  <section|Lagrange interpolation>

  The standard proofs of the Lagrange interpolation formula use the
  generalized Rolle's theorem.

  <\theorem>
    <em|[Classical Rolle's theorem]> Let <math|f> be differentiable and have
    two zeroes in an interval <math|[a,b]>. Then <math|f<rprime|'>> has a
    zero in <math|(a,b)>.
  </theorem>

  <\theorem>
    <label|GenRolle><em|[Classical generalized Rolle's theorem]> Let <math|f>
    be <math|n> times differentiable and have <math|n+1> zeroes in an
    interval <math|[a,b]>. Then <math|f<rsup|(n)>> has a zero in
    <math|[a,b]>.
  </theorem>

  <\proof>
    We only treat the case <math|n=2>. For concreteness say that <math|f=0>
    in 0, 1 and 2. By Rolle's theorem <math|f<rprime|'>=0> in
    <math|a\<in\>(0,1)> and <math|b\<in\>(1,2)>. Apply Rolle's theorem again
    to <math|f<rprime|'>>.
  </proof>

  This theorem can also be derived from the mean value theorem for divided
  differences.

  We now present the Lagrange polynomial as it can be found in numerical
  analysis textbooks; e.g.<nbsp><cite|BurdenFaires>.\ 

  <\definition>
    <label|def:Lagrange-poly>If <math|x<rsub|1>,\<ldots\>, x<rsub|n>> are
    <math|n> distinct numbers and <math|f:\<bbb-R\>\<rightarrow\>\<bbb-R\>>,
    then a unique polynomial <math|P<rsub|n>(x)> of degree at most <math|n-1>
    exists with <math|f(x<rsub|k>) = P(x<rsub|k>)>, for each <math|k =1,... ,
    n>. This polynomial is called the <em|Lagrange polynomial>. We also write
    <math|P<rsub|n>f> when the function <math|f> is not clear from the
    context.

    Explicitly, <math|P<rsub|n>(x)\<assign\><big|sum><rsub|j>f(x<rsub|j>)<big|prod><rsub|i,j\<neq\>i><frac|x-x<rsub|i>|x<rsub|j>-x<rsub|i>>>.
  </definition>

  <\theorem>
    <em|[Lagrange error formula]> Let <math|f> be <math|n> times
    differentable. Then for all <math|x>,

    <\equation*>
      \|f(x)-P<rsub|n>(x)\|\<leqslant\><frac|<big|prod>(x-x<rsub|k>)|n!>sup
      \|f<rsup|(n)>\|.
    </equation*>
  </theorem>

  The proof uses the generalized Rolle's theorem. Rolle's theorem is not
  constructively provable. However, an <math|\<varepsilon\>>-version of it
  <em|is> provable<nbsp><cite|Bishop/Bridges:1985>.\ 

  <\proposition>
    <label|eps-Rolle>Let <math|f> be continuously differentiable and
    <math|f(a)=f(b)=0>. Then there exists <math|x\<in\>(a,b)> such that
    <math|\|f<rprime|'>(x)\|\<leq\>\<varepsilon\>>.
  </proposition>

  This <math|\<varepsilon\>>-version can be used to prove an
  <math|\<varepsilon\>>-version of the generalized Rolle's theorem by
  constructing <math|a,b> as in the proof of
  Theorem<nbsp><reference|GenRolle>, but such that <math|><math|f(a)> and
  <math|f(b)> are small and then continuing the proof using the mean value
  theorem.

  <\proposition>
    Let <math|f> be <math|n> times differentiable and have <math|n+1> zeroes
    in an interval <math|[a,b]>. Then there exists <math|x\<in\>(a,b)> such
    that <math|\|f<rsup|(n)>(x)\|\<leq\>\<varepsilon\>>.
  </proposition>

  <\proof>
    We may assume that <math|b-a\<geqslant\>1>. By
    Proposition<nbsp><reference|eps-Rolle> there exists
    <math|x\<in\>(x<rsub|0>,x<rsub|1>)> such that
    <math|\|f<rprime|'>(x)\|\<leq\>\<varepsilon\>>. Similarly, there exists
    <math|y\<in\>(x<rsub|1>,x<rsub|2>)> such that
    <math|\|f<rprime|'>(y)\|\<leq\>\<varepsilon\>>. Hence there exists
    <math|z\<in\>(x,y)> such that

    <\equation*>
      \|f<rsup|<rprime|''>>(z)\|\<leq\>2<frac|\<varepsilon\>|a-b>+\<varepsilon\>\<leq\>3\<varepsilon\>.
    </equation*>

    By induction we see that there exists <math|w> such that
    <math|\|f<rsup|(n)>(w)\|\<less\>3<rsup|n-1>\<varepsilon\>>.
  </proof>

  <section|<label|generic>Generic zeros>

  A common method to transform a classical proof of a negative statement into
  a constructive one is by constructively proving the premisse. In this case,
  that premisse would be Rolle's theorem. However, to our knowledge there is
  no constructive proof that the derivative cannot fail to have a zero.

  Here we want to illustrate a different method. The idea is simple: instead
  of constructing a(n approximate) zero of the derivative we show that the
  formal space of zeros is non-trivial and then work with a generic zero.
  Actually carrying out this idea requires some preparations.

  First, we recall that Bishop's definition of differentiability includes
  continuity of the derivative, and its uniform continuity on compact
  intervals.

  Second, we use Palmgren's fully faithful embedding<nbsp><cite|Palmgren> of
  locally compact metric spaces into formal topological spaces.

  Third, we show prove Rolle's theorem as:

  <\proposition>
    <label|formal-Rolle><em|[Rolle]> The formal space
    <math|[f<rprime|'>=0]\<cap\>(a,b)> is not covered by the empty set.
  </proposition>

  We need a lemma.

  <\lemma>
    The interval <math|(a,b)> is connected.
  </lemma>

  <\proof>
    <strong|[Rolle]> The union of two closed sets is defined by the
    intersection of their complements. Hence, if <math|A> and <math|B> are
    closed sublocales of <math|(a,b)>, <math|A\<vee\>B=\<top\>>,
    <math|A\<wedge\>B=\<bot\>>, then <math|A=\<bot\>> or <math|B=\<bot\>>. To
    obtain a contradiction we assume that
    <with|mode|math|(f<rprime|'>=0)=\<bot\>>. Hence

    <\equation*>
      \<bot\>=(f<rprime|'>=0)=(f<rprime|'>\<geqslant\>0)\<wedge\>(f<rprime|'>\<leqslant\>0).
    </equation*>

    Moreover, <math|(f<rprime|'>\<geqslant\>0)\<vee\>(f<rprime|'>\<leqslant\>0)>
    is defined as the complement of <math|(f<rprime|'>\<less\>0)\<wedge\>(f<rprime|'>\<gtr\>0)=\<bot\>>,
    i.e.

    <\equation*>
      (f<rprime|'>\<geqslant\>0)\<vee\>(f<rprime|'>\<leqslant\>0)=\<top\>.
    </equation*>

    By connectedness either <math|(f<rprime|'>\<leqslant\>0)=\<bot\>> or
    <math|(f<rprime|'>\<leqslant\>0)=\<bot\>>. We assume the former, hence
    <math|u\<vartriangleleft\>V\<cup\>(f\<gtr\>0)> iff
    <math|u\<wedge\>\<bot\>\<vartriangleleft\>V>. Choosing <math|u=\<top\>>
    and <math|V=\<emptyset\>> we see that
    <math|(f<rprime|'>\<gtr\>0)=\<top\>>, i.e.
    <math|(f<rprime|'>\<gtr\>0)=(a,b)>. Now,
    <with|mode|math|(f<rprime|'>\<gtr\>0)=(a,b)> implies that
    <math|f(a)\<less\>f(b)>. A contradiction. Similarly,
    <math|(f<rprime|'>\<geq\>0)=\<bot\>> is contradictory. We see that
    <math|(f<rprime|'>=0)=\<bot\>> is contradictory.
  </proof>

  Consequently, to prove a negative geometric statement we may assume that
  there is a zero, as we will now show. The statements:

  <\enumerate>
    <item>for all <math|x> in <math|\<bbb-Q\>>,
    <math|\|f<rsup|(n)>(x)\|\<leqslant\>M>
    (i.e.<nbsp><math|\<exists\>x.\<phi\>(x)\<vdash\>\<bot\>)> and

    <item>there exists <math|x> in <math|\<bbb-Q\>>,
    <math|\|f(x)-P(x)\|\<gtr\><frac|<big|prod>(x-x<rsub|k>)|n+1!>M>.
  </enumerate>

  are geometric formulas over the definable object <math|\<bbb-Q\>>. By
  continuity the universal quantification can be extended to
  <math|\<bbb-R\>>.

  We will show that 2.<nbsp>is contradictory. Suppose that 2 holds. We add
  <math|n> generic zeroes of <math|f<rprime|'>> between the existing
  <math|n+1> zeroes for <math|f>. Then, in this new sheaf model,
  <math|Sh(X<rsub|1>)>, we add <math|n-1> generic zeroes for
  <math|f<rprime|''>>, etc. Hence, we move to a different sheaf model
  <math|n> times. In this last model, <math|Sh(X<rsub|n>)> we obtain a
  generic zero for <math|f<rsup|(n)>> in <math|(a,b)>. Once we have this zero
  we follow the classical argument for the lagrange error term to obtain
  <with|mode|math|\|f(x)-P(x)\|\<leqslant\><frac|<big|prod>(x-x<rsub|k>)|n!>M>.
  A contradiction in <math|Sh(X<rsub|n>)> since 2 is preserved by geometric
  morphisms. Hence the last space <math|X<rsub|n>> is trivial, contradicting
  Proposition<nbsp><reference|formal-Rolle>. Hence <math|Sh(X<rsub|n-1>)> is
  inconsitent, showing that <math|X<rsub|n-1>> is trivial. After <math|n>
  such steps we see that <math|X<rsub|1>>, i.e.<nbsp><math|(f=0)> must be the
  empty space. However, this contradicts Proposition<nbsp><reference|formal-Rolle>.
  We conclude that for all <math|x>, <math|\|f(x)-P(x)\|\<leqslant\>M>.

  <section|Polynomials>

  In order to proceed we need some theory about interpolation polynomials.
  The constructive theory of (interpolation) polynomials is somewhat
  complicated since <math|\<bbb-R\>[X]> is not a Euclidean ring. There is no
  zero test. We could try to extend the Lagrange polynomial to
  <math|\<bbb-R\>>. Instead, we show in Section<nbsp><reference|sec:HG> that
  the divided difference <math|C<rsup|n>[a,b]\<rightarrow\>C[a,b]<rsup|n>> is
  continuous for all <math|n>.

  Instead of <math|\<bbb-Q\>> we can choose any decidable subfield of the
  reals.

  <subsection|Intermezzo: defining differentiation <emdash> unfinished>

  <with|color|red|Not needed for the formalization.>

  We can try to <em|define> differentation using the divide difference. Here
  is a first unfinished attempt. For <math|\<alpha\>\<in\>\<bbb-N\><rsup|m>>,
  define <math|C<rsup|\<alpha\>>> to be the functions which are
  <math|\<alpha\>(i)>-times differentiable in the <math|i>th component.

  <\theorem>
    <math|f> is differentiable iff there exists <wide|f|~> such that
    <math|f(x+y)=f(x)+y<wide|f|~>(x,y)>. In this case,
    <math|f<rprime|'>(x)=<wide|f|~>(x,0)> and
    <math|f[x,x+y]=<frac|1|y>(f(x+y)-f(y))=<wide|f|~>(x,y)>.
  </theorem>

  <\proof>
    We do not need this for the formalization.
  </proof>

  <\lemma>
    <math|\<partial\><rsub|1>> has an right inverse
    <math|\<lambda\>x.<big|int><rsub|0><rsup|x>>.

    <math|<big|int><rsub|0><rsup|x>\<partial\>f=f(x)-f(0).>
  </lemma>

  <subsection|An axiomatic treatment of integration?>

  There are two formalitions of the integral. The corn formalization closely
  follows Bishop's treatment of the Riemann integral. As argued by Dieudonné,
  it seems better to treat the Cauchy integral (only continuous functions)
  and develop the full theory of Lebesgue integration when we need to go
  further. This is roughly the approach taken by Spitters and O'Connor who
  develop Cauchy integration theory for <math|C[0,1]>.

  One extends this to an integral on <math|C[a,b]>,
  <math|a,b\<in\>\<bbb-Q\>>, by a linear transformation. We define this
  integral for B-continuous functions <math|\<bbb-R\>\<rightarrow\>\<bbb-R\>>.\ 

  We could do the same for functions <math|\<bbb-R\>\<rightarrow\>X>, where
  <math|X> is a Banach space over <math|\<bbb-R\>>. This would allow
  currying: The integral <math|I\<times\>J\<rightarrow\>\<bbb-R\>> is the
  integral <math|I\<rightarrow\>C(J,\<bbb-R\>)>. The theory of integration in
  B-spaces should be completely analoguous to the existing development of
  Cauchy integration.

  Problem: <math|\<bbb-R\>\<rightarrow\>\<bbb-R\>> is not a Banach space,
  since the norm may become infinite. So, we choose to define integration on
  intervals. Note that we can always extend a continuous functions to a
  larger interval by extending it as a constant function. Whereas, the
  exponential function is a total function, to integrate it we only need its
  restriction to an interval.

  We now attempt an axiomatic treatment of integration and differentiation
  for continuous functions. However, this requires a formalization of
  continuous functions. Two such formalizations exist: one in Corn and one by
  O'Connor. There is a proof of their equivalence, but no common
  axiomatization.

  The derivative is defined as usual: <math|f<rprime|'>> is the derivative of
  <math|f> on <math|I> if for all <math|\<epsilon\>\<gtr\>0> there exists
  <math|\<delta\>\<gtr\>0> such that

  <\equation*>
    \|f(x)-f(y)-(x-y)f<rprime|'>(x)\|\<leqslant\>\<epsilon\>\|x-y\|<space|1em>when
    \|x-y\|\<leq\>\<delta\>.
  </equation*>

  We prove that the integral is defines a primitive. (this is possible by
  going via corn).

  In fact, I suspect that integration can be abstractly characterized as a
  primitive. However, it is not clear to me whether this abstraction is
  helpful. Depending on this decision the following are either axioms or
  lemma's. When done abstractly, we would have two implementations of this
  interface: Corn and Spitters/O'Connor.

  <math|F> is a primitive of <math|f> if <math|F> is differentiable and
  <math|F<rprime|'>=f>.\ 

  Primitives are defined upto a constant.\ 

  Axiom: every continuous function has a primitive. Every polynomial has a
  primitive.

  We define <math|<big|int><rsub|a><rsup|b>f=F(b)-F(a)>.\ 

  Lemma: The operation <math|<big|int>> is positive and linear. Corollary:
  <math|<big|int><rsub|a><rsup|b>f\<leq\>\|b-a\| \<\|\|\>f\<\|\|\>.>

  Change of variables: Let <math|G:\<bbb-R\>\<rightarrow\>\<bbb-R\>> be
  continuous<math|<big|int><rsub|a><rsup|b>(F\<circ\>G)*G<rprime|'> =
  <big|int><rsub|G(a)><rsup|G(b)>F>.

  We do not seem to need integration by parts for the current development.

  <subsection|Iterated integrals.>

  We prepare for the use of iterated integrals. For convience, we restrict to
  products of reals.

  <\definition>
    A function <math|\<bbb-R\><rsup|m>\<rightarrow\>X> is <em|B-continuous>
    (Bishop continuous) if it is uniformly continuous on each product of
    closed intervals.
  </definition>

  The follow two lemma's may not be needed in the formalization:

  <\lemma>
    A function <math|f:\<bbb-R\><rsup|m+1>\<rightarrow\>X> is B-continuous
    iff for all <math|x, <wide|y|\<vect\>>>, <math|f
    x:\<bbb-R\><rsup|m>\<rightarrow\>X> and
    <math|f<rsub|-><wide|y|\<vect\>>:\<bbb-R\>\<rightarrow\>X> are
    B-continuous.
  </lemma>

  <\lemma>
    Projections are B-continuous.

    If <math|f:\<bbb-R\><rsup|m>\<rightarrow\>\<bbb-R\>> is B-continuous and
    <math|h:\<bbb-R\><rsup|n>\<rightarrow\>X> is B-continuous, then partial
    composition <math|h\<circ\><rsub|i>f> is B-continuous from
    <math|\<bbb-R\><rsup|m+n-1>\<rightarrow\>X>.

    If <math|h:\<bbb-R\><rsup|n>\<rightarrow\>X> is B-continuous and
    <math|g:X\<rightarrow\>Y> is uniformly continuous, then the composition
    <math|g\<circ\>h:\<bbb-R\>\<rightarrow\>Y> is B-continuous.
  </lemma>

  <\lemma>
    <label|B-cont-prod>If <math|f:\<bbb-R\><rsup|m>\<rightarrow\>X> and
    <math|g:\<bbb-R\><rsup|m>\<rightarrow\>Y> B-continuous, then
    <math|(f,g):\<bbb-R\><rsup|m>\<rightarrow\>X\<times\>Y> continuous.
  </lemma>

  <\lemma>
    Let <math|f:\<bbb-R\><rsup|m+1>\<rightarrow\>\<bbb-R\>> and
    <math|g,h:\<bbb-R\><rsup|m>\<rightarrow\>[0,1]> be B-continuous. Then
    <math|\<lambda\><wide|y|\<vect\>>.<big|int><rsub|g(<wide|y|\<vect\>>)><rsup|h(<wide|y|\<vect\>>)>f(x,<wide|y|\<vect\>>)d
    x> is B-continuous.
  </lemma>

  <\proof>
    It suffices to prove that <math|\<lambda\><wide|y|\<vect\>>.<big|int><rsub|0><rsup|h(<wide|y|\<vect\>>)>f(x,<wide|y|\<vect\>>)d
    x> is B-continuous, by linearity.

    <math|\<lambda\><wide|y|\<vect\>>.<big|int><rsub|0><rsup|h(<wide|y|\<vect\>>)>f(x,<wide|y|\<vect\>>)>
    is the composition of <math|\<lambda\><wide|y|\<vect\>>.\<lambda\>x.f(x,<wide|y|\<vect\>>):\<bbb-R\><rsup|m>\<rightarrow\>C([0,1],\<bbb-R\>)>,
    <math|h> and

    <\equation*>
      <big|int><rsup|-><rsub|0>:[0,1]\<times\>C([0,1],\<bbb-R\>)\<rightarrow\>\<bbb-R\>.
    </equation*>

    This last function is <em|uniformly continuous.> The result follows from
    Lemma<nbsp><reference|B-cont-prod>.
  </proof>

  As a corollary, we can now perform iterated integration, as needed in
  Theorem<nbsp><reference|Thm:HG>.

  It should follow that for <math|f:\<bbb-R\><rsup|m>\<rightarrow\>\<bbb-R\>>
  integration over an interval <math|I> in the first coordinate is
  integration of the B-space valued function
  <math|f:\<bbb-R\>\<rightarrow\>\<bbb-R\><rsup|m>>. However, it is unclear
  whether we need this.

  \;

  <section|<label|sec:HG>Hermite-Genocchi formula>

  A more constructive and informative statement is possible using the
  Hermite-Genocchi formula. See<nbsp><cite|deBoor> for an overview and
  historical references. We will provide a closed formula for the error
  <math|f(x)-P<rsub|n>f(x)> in Formula<nbsp><reference|Genocchi>.

  The following text is aimed to be formalized, hence quite detailed, we
  expect to include more details as we go along.

  Given a set of <math|k + 1> data points <math|x<rsub|0>,...,x<rsub|k>>
  where no two <math|x<rsub|j>> are the same.

  <with|color|red|Such nodup lists are naturally defined using induction
  recursion.>

  Let <math|R> be a field and <math|f:R\<rightarrow\>R>. The interpolation
  polynomial in the Newton form is a linear combination of Newton basis
  polynomials

  <\equation*>
    N(x) := <big|sum><rsub|j=0><rsup|k>a<rsub|j> n<rsub|j>(x)
  </equation*>

  with the Newton basis polynomials defined as

  <\equation*>
    n<rsub|j>(x) := <big|prod><rsub|i=0><rsup|j-1> (x - x<rsub|i>)
  </equation*>

  and the coefficients defined as <math|a<rsub|j> :=
  f[x<rsub|j>,...,x<rsub|0>]>, where <math|f[x<rsub|j>,...,x<rsub|0>]> is the
  notation for <em|divided differences>, defined recursively by:

  <\equation*>
    f[a]=f(a)
  </equation*>

  <\equation*>
    f[a,b] = <frac|f(a) - f(b)|a-b>\ 
  </equation*>

  <\equation*>
    f[a,b,c] = <frac|f[a,c]-f[b,c]|a- b>
  </equation*>

  and in general, <math|f[a:b:l]\<assign\><frac|f[a:l]-f[b:l]|a-b>>. Here
  <math|a:l> denotes the concatenation of an element to a list, the list may
  be empty.

  Thus the Newton polynomial can be written as

  <\equation*>
    N(x) := f[x<rsub|0>] +f [x<rsub|1>,x<rsub|0>](x-x<rsub|0>) + \<cdots\> +
    f[x<rsub|k>,...,x<rsub|0>](x-x<rsub|0>)(x-x<rsub|1>)\<cdots\>(x-x<rsub|k-1>).<label|Newton-coeff>
  </equation*>

  We use the following lemma.

  <\lemma>
    If <math|deg f\<leq\>n> and <math|f(a)=0>, then <math|f=(x-a)p>.
  </lemma>

  <\proof>
    We prove this by induction. For <math|n=0>, there is nothing to prove.\ 

    Let <math|f=b<rsub|n>x<rsup|n>+ \<ldots\>.+b<rsub|0>>, then
    <math|f=b<rsub|n>x<rsup|n-1>(x-a)+r> and <math|deg r\<leq\>n-1>.
    Moreover, <math|r(a)=0>. So <with|mode|math|r=(x-a)p> and
    <math|f=(b<rsub|n>x<rsup|n-1>+p)(x-a).>
  </proof>

  <\lemma>
    If <math|deg f,deg g\<leq\>n> and <math|f,g> share <math|n+1> zeroes,
    then <math|f=g>.
  </lemma>

  <\proof>
    By the previous lemma there exists <math|h> such that
    <math|h<big|prod>(x-a<rsub|i>)=f-g>. Hence,

    <\equation*>
      (n+1)deg h=deg( f-g)\<leqslant\>n.
    </equation*>

    Consequently, <math|deg h=0>, so <math|h=0> and <math|f-g=0>.
  </proof>

  <\lemma>
    The Newton polynomial coincides with the Lagrange polynomial.
  </lemma>

  <\proof>
    We claim that for all <math|x\<in\>l=(x<rsub|k>,\<ldots\>,x<rsub|0>)>,
    <math|N<rsub|l>(x)=f(x)>. Proof by induction on the length <math|k+1> of
    the sequence. <math|k=0> is direct.

    For the case <with|mode|math|l=(x<rsub|k>,\<ldots\>,x<rsub|0>)>,
    i.e.<nbsp><math|k+1>, we consider the last coefficient of
    <math|N<rsub|l>> evaluated at <math|x<rsub|k>>.

    <\eqnarray>
      <tformat|<table|<row|<cell|>|<cell|f[x<rsub|k>,...,x<rsub|0>](x<rsub|k>-x<rsub|0>)\<cdots\>(x<rsub|k>-x<rsub|k-1>)>|<cell|=>>|<row|<cell|>|<cell|-(f[x<rsub|k-1>,x<rsub|k-2>,...,x<rsub|0>]-f[x<rsub|k>,x<rsub|k-2>,...,x<rsub|0>])(x<rsub|k>-x<rsub|0>)\<cdots\>(x<rsub|k>-x<rsub|k-2>)>|<cell|>>>>
    </eqnarray>

    The first term is the penultimate term of <math|N<rsub|l>(x<rsub|k>)>,
    which is defined as

    <with|mode|math|N<rsub|l>(x<rsub|k>) := f[x<rsub|0>] +f
    [x<rsub|1>,x<rsub|0>](x<rsub|k>-x<rsub|0>) + \<cdots\> +
    f[x<rsub|k>,...,x<rsub|0>](x<rsub|k>-x<rsub|0>)\<cdots\>(x<rsub|k>-x<rsub|k-1>).>

    Hence, <math|N<rsub|l>(x<rsub|k>)=N<rsub|l-x<rsub|k-1>>(x<rsub|k>)=f(x<rsub|k>)>.

    We also have <math|N<rsub|l>(x<rsub|i>)=f(x<rsub|i>)> for
    <math|i\<less\>k>, by equation<nbsp><reference|Newton-coeff>,
    <with|mode|math|N<rsub|l>(x<rsub|i>)=N<rsub|l-x<rsub|k>>(x<rsub|i>)=f(x<rsub|i>)>.\ 

    We are done by induction.

    <with|color|red|Use the range descriptions in the bigops library to
    handle the removal of an element from a list?>
  </proof>

  <\corollary>
    The divided difference <math|f[a<rsub|n>,\<ldots\>,a<rsub|1>]> is the
    coefficient of <math|x<rsup|n>> in the (Newton) polynomial that
    interpolates <math|f> at <with|mode|math|a<rsub|1>,\<ldots\>,a<rsub|n>>.
  </corollary>

  <\proposition>
    <label|prop:divdiff>The divided difference is linear and satisfies the
    Leibniz rule:

    <\eqnarray>
      <tformat|<table|<row|<cell|(f+g)[x<rsub|n>,\<ldots\>,x<rsub|0>]>|<cell|=>|<cell|f[x<rsub|n>,\<ldots\>,x<rsub|0>]
      + g[x<rsub|n>,\<ldots\>,x<rsub|0>];>>|<row|<cell| (\<lambda\>\<cdot\>
      f)[x<rsub|n>,\<ldots\>,x<rsub|0>]>|<cell|=>|<cell|\<lambda\>\<cdot\>
      f[x<rsub|n>,\<ldots\>,x<rsub|0>];>>|<row|<cell|(f\<cdot\>
      g)[x<rsub|n>,\<ldots\>,x<rsub|0>] >|<cell|=>|<cell|
      f[x<rsub|0>]\<cdot\> g[x<rsub|n>,\<ldots\>,x<rsub|0>] +
      f[x<rsub|1>,x<rsub|0>]\<cdot\> g[x<rsub|n>,\<ldots\>,x<rsub|1>] +
      \<ldots\>+ f[x<rsub|n>,\<ldots\>,x<rsub|0>]\<cdot\> g[x<rsub|n>].>>>>
    </eqnarray>
  </proposition>

  <with|color|red|We do not need the last fact in the formalization.>

  <\lemma>
    <\em>
      [Ampere] Each function <math|f[l]> is symmetric in the variables.
    </em>
  </lemma>

  <\proof>
    The definition of the Lagrange poly is.

    An alternative proof uses the representation of a permutation of a
    composition of two-element permutations, together with induction on the
    length of <math|l>. For <math|\<pi\><rsub|a b>> the lemma is clear. For
    any other permutation it follows by induction and a little computation
    for <math|\<pi\><rsub|b x>f[a:l]>.
  </proof>

  <with|color|red|Define permutations of lists as a setoid relation and show
  that <math|[ -]> is a morphism for this.>

  At this point we need the fundamental theorem of calculus. Hence we assume
  that <math|R=\<bbb-R\>>.

  <\lemma>
    If <math|a\<less\>b>, then <math|C[a,b]> is an algebra over the ring
    <math|\<bbb-R\>>.
  </lemma>

  We do not need that it is an algebra over the field <math|\<bbb-R\>>.

  <\definition>
    A <em|derivation> on an <math|R>-algebra is a <math|R>-linear map
    satisfying the Leibniz rule:

    <\equation*>
      D(a b) = (D a)b + a(D b).
    </equation*>
  </definition>

  <\definition>
    Let <math|C<rsup|\<infty\>>[a,b]> be the functions <math|f> such that
    <math|f<rsup|(n)>> exists for all <math|n>.
  </definition>

  <\proposition>
    The derivative is a derivation on <math|C<rsup|\<infty\>>[a,b]>.
  </proposition>

  <\definition>
    For \ <math|a\<less\>b> and <with|mode|math|c\<less\>d>,

    <\equation*>
      L<rsub|a b c d>(f)\<assign\>\<lambda\>t.f(c+(d-c)(<frac|t-a|b-a>)).
    </equation*>
  </definition>

  <\lemma>
    <math|L<rsub|a b c d > >maps <math|C<rsup|\<infty\>>[c,d]> to
    <math|C<rsup|\<infty\>>[a,b]>.
  </lemma>

  Consider the following motivation which will only be made precise in
  Thm<nbsp><reference|Thm:HG>. We have,

  <\equation*>
    f[a,b] = <big|int><rsub|0><rsup|1>f<rprime|'>(a+(b-a)t)
    dt=<big|int><rsub|0><rsup|1>L<rsub|0 1 a b>(f<rprime|'>).
  </equation*>

  \;

  <\eqnarray>
    <tformat|<table|<row|<cell|f[a,b,c]>|<cell|=>|<cell|<big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|u>
    f<rprime|''>(a+(b-a)t+(c-b) u) d t d u<label|form:explicit>>>>>
  </eqnarray>

  Cf. [dB, p64] and note that

  <\equation*>
    a+(b-a)t+(c-b) u=(1-t)a+(t-u)b+u c.
  </equation*>

  Moreover, <with|mode|math|(1-t)+(t-u)+u =1>.\ 

  The general formula can be put in a symmetric form

  <\equation*>
    f[a<rsub|0>,...,a<rsub|n>]= <big|int><big|int><rsub|n>f<rsup|(n)>(t<rsub|0>
    a<rsub|0>+ ... + t<rsub|n>a<rsub|n>) d t<rsub|1>\<cdots\>d t<rsub|n>
  </equation*>

  with <math|t<rsub|0>+\<cdots\>+t<rsub|n> = 1> and
  <math|0\<leqslant\>t<rsub|i> \<leqslant\>1>. Note the extra variable. We
  make the side condition explicit:

  <\theorem>
    <label|Thm:HG>

    <\equation>
      <tabular|<tformat|<table|<row|<cell|f[a<rsub|0>,\<ldots\>,a<rsub|n>]>|<cell|=>|<cell|<big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-t<rsub|1>><big|int><rsub|0><rsup|1-(t<rsub|1>+t<rsub|2>)><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n-1>t<rsub|j>)>
      f<rsup|(n)>(<big|sum>t<rsub|i>a<rsub|i>) d t<rsub|n> \<cdots\>d
      t<rsub|1>.<label|Hermite-Genocchi>>>>>>
    </equation>

    where <math|t<rsub|0>\<assign\>1-(<big|sum><rsub|j=1><rsup|n>t<rsub|j>)>.
    Let <with|mode|math|<big|int><rsup|S><rsub|n>> denote this symmetric
    integral.
  </theorem>

  <\proof>
    This formula is proved by induction on <math|n>;
    see<nbsp><cite|Alexander>. In fact the proof there is inexplicit about
    the order of variables.

    For <math|n=0>, there is nothing to prove.

    For the inductive step consider

    <\equation*>
      f[a<rsub|0>,\<ldots\>,a<rsub|n+1>]=<frac|f[a<rsub|1>,\<ldots\>,a<rsub|n+1>]-f[a<rsub|0>,\<ldots\>,a<rsub|n>]|a<rsub|n+1>-a<rsub|0>>.
    </equation*>

    By symmetry,

    <\equation*>
      f[a<rsub|0>,\<ldots\>,a<rsub|n+1>]=<frac|f[a<rsub|n+1>,
      a<rsub|1>,\<ldots\>,a<rsub|n>]-f[a<rsub|0>,\<ldots\>,a<rsub|n>]|a<rsub|n+1>-a<rsub|0>>.
    </equation*>

    By induction, <with|mode|math|f[a<rsub|0>,\<ldots\>,a<rsub|n+1>]> equals

    <\eqnarray*>
      <tformat|<table|<row|<cell|>|<cell|<frac|1|a<rsub|n+1>-a<rsub|0>>>|<cell|<left|(><big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n-1>t<rsub|j>)>
      f<rsup|(n)>(t<rsub|0>a<rsub|n+1>+\<cdots\>+t<rsub|n>a<rsub|n>) d
      t<rsub|n> \<cdots\>d t<rsub|1>>>|<row|<cell|>|<cell|->|<cell|
      <big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n-1>t<rsub|j>)>
      f<rsup|(n)>(t<rsub|0>a<rsub|0>+\<cdots\>+t<rsub|n>a<rsub|n>)d t<rsub|n>
      \<cdots\>d t<rsub|1><right|)>,>>>>
    </eqnarray*>

    where <math|t<rsub|0>\<assign\>1-(<big|sum><rsub|j=1><rsup|n>t<rsub|j>)>.

    By the fundamental theorem of calculus this is

    <\equation*>
      <tabular|<tformat|<table|<row|<cell|>|<cell|<frac|1|a<rsub|n+1>-a<rsub|0>>>|<cell|<big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n-1>t<rsub|j>)>
      <big|int><rsup|t<rsub|0>a<rsub|n+1>+\<cdots\>+t<rsub|n>a<rsub|n>><rsub|t<rsub|0>a<rsub|0>+\<cdots\>+t<rsub|n>a<rsub|n>>f<rsup|(n+1)>(\<xi\>)
      d\<xi\>d t<rsub|n> \<cdots\>d t<rsub|1>.>>>>>
    </equation*>

    Make the change of variable <math|\<xi\>=t<rsub|0>a<rsub|0>+\<cdots\>t<rsub|n>a<rsub|n>+t<rsub|n+1>(a<rsub|n+1>-a<rsub|0>)>.
    Then for all <math|g>,

    <\equation*>
      <big|int>g d \<xi\>=(a<rsub|n+1>-a<rsub|0>)<big|int><rsub|0><rsup|t<rsub|0>>g
      d t<rsub|n+1>.
    </equation*>

    We conclude that\ 

    <\equation*>
      <tabular|<tformat|<table|<row|<cell|<big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n>t<rsub|j>)>
      <big|int><rsup|t<rsub|0>><rsub|0>f<rsup|(n+1)>(t<rsub|0>a<rsub|0>+\<cdots\>+t<rsub|n>a<rsub|n>+t<rsub|n+1>(a<rsub|n+1>-a<rsub|0>))
      d t<rsub|n+1>d t<rsub|n> \<cdots\>d t<rsub|1>.>>>>>
    </equation*>

    Hence,

    <\equation*>
      <tabular|<tformat|<table|<row|<cell|<big|int><rsub|0><rsup|1><big|int><rsub|0><rsup|1-(<big|sum><rsub|j=1><rsup|n>t<rsub|j>)>
      f<rsup|(n+1)>(<wide|t<rsub|0>|^>a<rsub|0>+\<cdots\>+t<rsub|n+1>a<rsub|n+1>)
      d t<rsub|n+1>d t<rsub|n> \<cdots\>d t<rsub|1>,>>>>>
    </equation*>

    where <math|<wide|t<rsub|0>|^>\<assign\>1-(<big|sum><rsub|j=1><rsup|n+1>t<rsub|j>).>
  </proof>

  The Hermite-Genocchi formula is an integral formulation of the mean value
  theorem for divided differences.

  <\corollary>
    <label|cor:weight><with|mode|math|<big|int><rsup|S><rsub|n>1 d
    t<rsub|1>\<cdots\>d t<rsub|n-1>=<frac|1|(n-1)!>>.
  </corollary>

  <\proof>
    Choose <with|mode|math|a<rsub|1>,\<ldots\>,a<rsub|n>> arbitrary, but
    distinct. Let <math|a> be the list <math|(0,a<rsub|1>,\<ldots\>,a<rsub|n>)>.
    Define the polynomial <with|mode|math|g<rsub|n\<assign\>><frac|1|(n-1)!><big|prod>(x-a<rsub|i>)>.
    Then <math|g<rsup|(n-1)>=1>. The polynomial <math|g<rsub|n>> is the
    Lagrange polynomial for the list <math|a>, so
    <math|g<rsub|n>[a]=<frac|1|(n-1)!>>. The corollary follows from
    Hermite-Genocchi.
  </proof>

  <\lemma>
    The function <math|f[a<rsub|1>,\<ldots\>,a<rsub|n>]> is continuous on
    <math|I<rsup|n>> and <math|f[a,\<ldots\>,a]=f<rsup|(n-1)>(a)/n!>.
  </lemma>

  <\proof>
    We consider <math|I<rsup|n>> with the metric
    <math|d((a<rsub|i>),(b<rsub|i>))=max<rsub|i>\|a<rsub|i>-b<rsub|i>\|>.

    Let <math|0\<leqslant\>t<rsub|i>\<leqslant\>1> and
    <math|<big|sum>t<rsub|i>=1>, then

    <\equation*>
      <big|sum>t<rsub|i>a<rsub|i>-<big|sum>t<rsub|i>b<rsub|i>=<big|sum>t<rsub|i>(a<rsub|i>-b<rsub|i>)\<leq\><big|sum><rsub|i>t<rsub|i>max<rsub|i>\|a<rsub|i>-b<rsub|i>\|=max<rsub|i>\|a<rsub|i>-b<rsub|i>\|.
    </equation*>

    This proves continuity.

    We now extend <math|f[\<ldots\>]> to all, possibly non-distinct,
    sequences.

    By continuity,

    <\eqnarray*>
      <tformat|<table|<row|<cell|f[a,\<ldots\>,a]>|<cell|=>|<cell|<big|int><big|int><rsub|n-1>f<rsup|(n-1)>(a)
      d u<rsub|1>\<cdots\>d u<rsub|n-1>>>|<row|<cell|>|<cell|=>|<cell|f<rsup|(n-1)>(a)<big|int><big|int><rsub|n-1>1
      d u<rsub|1>\<cdots\>d u<rsub|n-1>>>|<row|<cell|>|<cell|=>|<cell|f<rsup|(n-1)>(a)<frac|1|(n-1)!>.>>>>
    </eqnarray*>
  </proof>

  <\proposition>
    [dB, p63] We have

    <\equation>
      f(x)-P <rsub|n>f(x)=<left|(><big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)<right|)>f[x<rsub|1>,\<ldots\>,x<rsub|n>,x]<label|Genocchi>
    </equation>
  </proposition>

  and hence, by<nbsp>(<reference|Hermite-Genocchi>),

  <\equation>
    f(x)-P <rsub|n>f(x)=<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)<big|int><rsup|S><rsub|n>f<rsup|(n)>(t<rsub|1>
    x<rsub|1>+ ... + t<rsub|n>x<rsub|n>+t<rsub|0> x) d u<rsub|1>\<cdots\>d
    u<rsub|n><label|Genocchi2>
  </equation>

  with <math|t<rsub|0>+\<cdots\>+t<rsub|n> = 1> and
  <math|0\<leqslant\>t<rsub|i> \<leqslant\>1>.

  <\proof>
    We prove by induction that

    <\equation*>
      f[x<rsub|1>,\<ldots\>,x<rsub|n>]=<big|sum><rsub|j=1><rsup|n><frac|f(x<rsub|j>)|<big|prod><rsub|i,i\<neq\>j>(x<rsub|j>-x<rsub|i>)>.
    </equation*>

    Also,

    <\eqnarray>
      <tformat|<table|<row|<cell|<frac|f(x)-P
      <rsub|n>f(x)|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>>|<cell|=>|<cell|<frac|f(x)-<big|sum><rsub|j>f(x<rsub|j>)<big|prod><rsub|i,j\<neq\>i><frac|x-x<rsub|j>|x<rsub|i>-x<rsub|j>>|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>>>|<row|<cell|>|<cell|=>|<cell|<frac|f(x)|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>-<frac|<big|sum><rsub|j>f(x<rsub|j>)<big|prod><rsub|i,j\<neq\>i><frac|x-x<rsub|j>|x<rsub|i>-x<rsub|j>>|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>>>|<row|<cell|>|<cell|=>|<cell|<frac|f(x)|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>-<frac|<big|sum><rsub|j>f(x<rsub|j>)|<big|prod><rsub|i,j\<neq\>i>(x<rsub|i>-x<rsub|j>)(x-x<rsub|i>)>>>|<row|<cell|>|<cell|<above|=|[x<rsub|n+1>\<assign\>x]>>|<cell|<big|sum><rsub|j=1><rsup|n+1><frac|f(x<rsub|j>)|<big|prod><rsub|i,i\<neq\>j>(x<rsub|j>-x<rsub|i>)>.>>>>
    </eqnarray>
  </proof>

  The following is direct. <with|color|red|Not needed for the formalization.>

  <\corollary>
    If <math|f(x<rsub|i>)=0> and <math|f<rsup|(n)>\<geqslant\>0>, then the
    sign of <math|f(x)> equals that of <with|mode|math|<big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)>.
  </corollary>

  <\corollary>
    <math|\|f(x)-P<rsub|n>(x)\|\<leqslant\><frac|<big|prod>(x-x<rsub|k>)|n!>\<\|\|\>f<rsup|(n)>\<\|\|\>>
  </corollary>

  <\proof>
    We write <math|u<rsub|0>\<assign\>x>. By
    Corollary<nbsp><reference|cor:weight> and
    Formula<nbsp><reference|Genocchi2>,

    <\equation*>
      \|f(x)-P <rsub|n>f(x)\|=<left|\|><big|int><rsup|S><rsub|n+1>f<rsup|(n)>(u<rsub|0>
      x<rsub|0>+ ... + u<rsub|n>x<rsub|n>) d u<rsub|0>\<cdots\>d
      u<rsub|n><right|\|><big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>)\<leqslant\><frac|M|n!><big|prod><rsub|i=1><rsup|n>(x-x<rsub|i>).
    </equation*>
  </proof>

  This allows us to proof the error estimates for the Newton-Cotes formulas.
  In particular, we can do so for Simpson's rule.

  <\corollary>
    <em|[Simpson's rule]>

    <\equation*>
      \|<big|int><rsub|a><rsup|b> f(x) <space|0.25spc>d x
      -<frac|b-a|6><left|[>f(a) + 4f<left|(><frac|a+b|2><right|)>+f(b)<right|]>\|\<leqslant\><frac|(b-a)<rsup|5>|2880>\<\|\|\>F<rsup|(4)>\<\|\|\>.
    </equation*>
  </corollary>

  <\proof>
    The right handside is the integral of the lagrange polynomial
    <math|P<rsub|3>> at <math|a,<frac|a+b|2>,b>.
    See<nbsp><cite|BurdenFaires>. For the error we adopt the proof
    in<nbsp><cite|SuliMayers>, but replace the use of Rolle's theorem and the
    Mean Value Theorem by the Hermite-Genocchi formula. Define
    <math|F(t)\<assign\>f(<frac|a+b|2>+<frac|b-a|2>t)>. This reduces the
    problem to showing that <with|mode|math|\|<big|int><rsub|-1><rsup|1>F(\<tau\>)d
    \<tau\>-<frac|1|3>(F(-1)+4F(0)+F(1)]\|\<leqslant\>N/90>, where
    <math|N\<assign\>\<\|\|\>F<rsup|(4)>\<\|\|\>.>

    Define

    <\equation*>
      G(t)=<big|int><rsub|-t><rsup|t>F(\<tau\>)d
      \<tau\>-<frac|t|3>(F(-t)+4F(0)+F(t)]
    </equation*>

    We need to prove that <math|90G(1)\<leqslant\>N>. To do so, define
    <math|H(t)\<assign\>G(t)-t<rsup|5>G(1)>. Then

    <\equation*>
      H(0)=H(1)=H<rprime|'>(0)=H<rprime|''>(0)=0.
    </equation*>

    Hence, <math|H[0,0,0,1]=-(H[0,0,0]-H[0,0,1])=0+( \<um\>H[0,0]+H[0,1])=0>.

    Moreover, <math|H<rsup|(3)>(t)=-<frac|t|3>(F<rsup|(3)>(t)-F<rsup|(3)>(-t))-60t<rsup|2>G(1)=-<frac|t|3>(<big|int><rsub|-t><rsup|t>F<rsup|(4)>)-60t<rsup|2>G(1)>.

    This shows that

    <\eqnarray>
      <tformat|<table|<row|<cell|0=H[0,0,0,1]>|<cell|=>|<cell|<big|int><rsup|1><rsub|0>H<rsup|(3)>>>|<row|<cell|>|<cell|=
      >|<cell|<big|int><rsub|0><rsup|1>-<frac|t|3>(<big|int><rsub|-t><rsup|t>F<rsup|(4)>)-60t<rsup|2>G(1)>>|<row|<cell|>|<cell|\<geqslant\>>|<cell|<big|int><rsub|0><rsup|1>-<frac|t|3>2tN-60t<rsup|2>G(1)>>|<row|<cell|>|<cell|=>|<cell|-<frac|2|3>(N+90G(1))<big|int><rsub|0><rsup|1>t<rsup|2>>>|<row|<cell|>|<cell|=
      >|<cell|-<frac|2|3>(N+90G(1))<frac|1|3>.>>>>
    </eqnarray>

    Hence, <math|N\<geqslant\>-90G(1)>. Similarly,
    <with|mode|math|0\<leqslant\>-<frac|2|9>(-N+90G(1))>. Consequently,
    <math|90G(1)\<leqslant\>N>. We conclude that
    <math|\|90G(1)\|\<leqslant\>N>.
  </proof>

  <\proposition>
    <em|[Composite Simpson rule]> For <math|n> even,

    <\equation*>
      <big|int><rsub|a><rsup|b> f(x) <space|0.25spc>dx\<approx\>
      <frac|h|3><left|[>f(x<rsub|0>)+2<big|sum><rsub|j=1><rsup|n/2-1>f(x<rsub|2j>)+
      4<big|sum><rsub|j=1><rsup|n/2>f(x<rsub|2j-1>)+f(x<rsub|n>) <right|]>,
    </equation*>

    with error

    <\equation*>
      <frac|h<rsup|4>|180>(b-a) max<rsub|\<xi\>\<in\>[a,b]>
      \|f<rsup|(4)>(\<xi\>)\|.
    </equation*>
  </proposition>

  <\proposition>
    The following functions are in <math|C<rsup|\<infty\>>>:
    <math|sin,cos,exp>, polynomials and there compositions. Also, addition
    and multiplication of <math|C<rsup|\<infty\>>> functions are
    <math|C<rsup|\<infty\>>>.
  </proposition>

  <with|color|red|Apply to the elliptic integral.>

  <section|Conclusion>

  We have analysed the use of lagrange polynomials, a key ingredient in
  numerical integration and differentiation.

  The classical proof uses a generalized Rolle's theorem. We provided an
  approximate version of Rolle's theorem which suffices for the application
  the the Lagrange error formula. We also provide a constructive
  interpretation of this proof using sheaf models. The strategy is to turn a
  classical proof of a (negative) geometric statement into a constructive
  proof by turning classical existence of a point into constructive
  non-triviality of the formal space of all such points. We believe that this
  is quite a general technique. For instance, the <math|f<rsup|-1>({sup f})>
  is not covered by the empty set since the image of the compact space
  <math|[a,b]> is compact. A classical proof that a constructive proof of
  such a statement exists is provided by Barr's theorem. However, Barr's
  theorem does not provide a clue how to actually find the constructive
  proof.\ 

  Taylor<nbsp><cite|Taylor> already proposed to consider the intermediate
  values as a space. Vickers<nbsp><cite|CViet> provides a localic treatment
  of Rolle's theorem by showing that <math|inf<rsub|[a,b]> \|f<rprime|'>\|=0>
  if <math|f(a)=f(b)=0>. In our work on Banach
  algebras<nbsp><cite|banach-algebra> we also used iterated forcing to obtain
  a constructive result.

  Stolzenberg and Bridger<nbsp><cite|BridgerStolzenberg> argue that the law
  of bounded change:

  If <math|f> is uniformly differentiable and
  <math|A\<leqslant\>f<rprime|'>\<leqslant\>B> on <math|[a,b]>, then

  <\equation*>
    A(b-a)\<leqslant\>f(b)-f(a)\<leqslant\>B(b-a).
  </equation*>

  can often be used to replace the mean value theorem. The treatment above
  suggests an extension of Bridger-Stolzenberg idea to higher-order
  derivations. For instance, we define <math|f> to be twice differentiable on
  <math|I> iff there are continuous functions <math|f(a,b)> on
  <math|I<rsup|2>> and <math|f(a,b,c)> on <math|I<rsup|3>> with

  <\equation*>
    f(x) = f(a) + (x-a)f(a,x)
  </equation*>

  <\equation*>
    f(x) = f(a) + (x-a)f(a,b) + (x-a)(x-b)f(a,b,x).
  </equation*>

  Similar ideas are needed to develop differentation over general
  fields<nbsp><cite|DiffFields>. As observed there:

  <\quotation>
    The proofs are `algebraic' in nature and in this way become often simpler
    and more transparent even than the usual proofs in
    <math|\<bbb-R\><rsup|n>> because we avoid the repeated use of the Mean
    Value Theorem (or of the Fundamental Theorem) which are no longer needed
    once they are incorporated in [the definition of the derivative by a
    difference quotient].
  </quotation>

  The proof development above also shows another feature. We construct a
  certain function in a decidable algebraic setting. Then we prove that the
  function is continuous and extend to the completion. This should allow us
  to conveniently combine the ssreflect library with a library for continuous
  mathematics.

  <section|Acknowledgements>

  I would like to thank Thierry Coquand and Henri Lombardi for pointing me
  towards the Genocchi formula.

  <\bibliography|bib|alpha|lagrange.bib>
    <\bib-list|BGN04>
      <bibitem*|Ale><label|bib-Alexander>R.K. Alexander. <newblock>The
      Hermite-Genocchi formula.

      <bibitem*|BB85><label|bib-Bishop/Bridges:1985>Errett Bishop and Douglas
      Bridges. <newblock><with|font-shape|italic|Constructive analysis>,
      volume 279 of <with|font-shape|italic|Grundlehren der Mathematischen
      Wissenschaften>. <newblock>Springer-Verlag, 1985.

      <bibitem*|BGN04><label|bib-DiffFields>W.<nbsp>Bertram,
      H.<nbsp>Glöckner, and K.-H. Neeb. <newblock>Differential calculus over
      general base fields and rings. <newblock><with|font-shape|italic|Expo.
      Math.>, 22(3):213--282, 2004.

      <bibitem*|BS99><label|bib-BridgerStolzenberg>Mark Bridger and Gabriel
      Stolzenberg. <newblock>Uniform calculus and the law of bounded change.
      <newblock><with|font-shape|italic|Amer. Math. Monthly>,
      106(7):628--635, 1999.

      <bibitem*|CS><label|bib-banach-algebra>Thierry Coquand and Bas
      Spitters. <newblock>A constructive theory of Banach algebras.
      <newblock>to appear.

      <bibitem*|dB05><label|bib-deBoor>Carl de<nbsp>Boor. <newblock>Divided
      differences. <newblock><with|font-shape|italic|Surv. Approx. Theory>,
      1:46--69, 2005.

      <bibitem*|FB98><label|bib-BurdenFaires>J.<nbsp>Douglas Faires and
      Richard Burden. <newblock><with|font-shape|italic|Numerical methods>.
      <newblock>Brooks/Cole Publishing Co., Pacific Grove, CA, second
      edition, 1998.

      <bibitem*|Pal07><label|bib-Palmgren>Erik Palmgren. <newblock>A
      constructive and functorial embedding of locally compact metric spaces
      into locales. <newblock><with|font-shape|italic|Topology Appl.>,
      154(9):1854--1880, 2007.

      <bibitem*|SM03><label|bib-SuliMayers>Endre Süli and David<nbsp>F.
      Mayers. <newblock><with|font-shape|italic|An introduction to numerical
      analysis>. <newblock>Cambridge University Press, Cambridge, 2003.

      <bibitem*|Tay05><label|bib-Taylor>Paul Taylor. <newblock>A lambda
      calculus for real analysis. <newblock>In <with|font-shape|italic|CCA>,
      pages 227--266, 2005.

      <bibitem*|Vic09><label|bib-CViet>Steven Vickers. <newblock>The
      connected Vietoris powerlocale. <newblock><with|font-shape|italic|Topology
      and its Applications>, 156(11):1886--1910, 2009.
    </bib-list>
  </bibliography>
</body>

<\initial>
  <\collection>
    <associate|info-flag|detailed>
    <associate|page-medium|paper>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|B-cont-prod|<tuple|14|4>>
    <associate|GenRolle|<tuple|2|1>>
    <associate|Genocchi|<tuple|2|7>>
    <associate|Genocchi2|<tuple|3|7>>
    <associate|Hermite-Genocchi|<tuple|1|6>>
    <associate|Newton-coeff|<tuple|5|4>>
    <associate|Thm:HG|<tuple|28|6>>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|7|10>>
    <associate|auto-11|<tuple|7|9>>
    <associate|auto-2|<tuple|2|1>>
    <associate|auto-3|<tuple|3|2>>
    <associate|auto-4|<tuple|4|3>>
    <associate|auto-5|<tuple|4.1|3>>
    <associate|auto-6|<tuple|4.2|3>>
    <associate|auto-7|<tuple|4.3|4>>
    <associate|auto-8|<tuple|5|9>>
    <associate|auto-9|<tuple|6|10>>
    <associate|bib-Alexander|<tuple|Ale|10>>
    <associate|bib-Bishop/Bridges:1985|<tuple|BB85|10>>
    <associate|bib-BridgerStolzenberg|<tuple|BS99|10>>
    <associate|bib-BurdenFaires|<tuple|FB98|10>>
    <associate|bib-CViet|<tuple|Vic09|10>>
    <associate|bib-DiffFields|<tuple|BGN04|10>>
    <associate|bib-FairesBurden|<tuple|FB98b|4>>
    <associate|bib-Palmgren|<tuple|Pal07|10>>
    <associate|bib-SuliMayers|<tuple|SM03|10>>
    <associate|bib-Taylor|<tuple|Tay05|10>>
    <associate|bib-banach-algebra|<tuple|CS|10>>
    <associate|bib-deBoor|<tuple|dB05|10>>
    <associate|cor:weight|<tuple|29|7>>
    <associate|def:Lagrange-poly|<tuple|3|1>>
    <associate|eps-Rolle|<tuple|5|1>>
    <associate|footnote-1|<tuple|1|2>>
    <associate|footnr-1|<tuple|1|2>>
    <associate|form:explicit|<tuple|27|6>>
    <associate|formal-Rolle|<tuple|7|2>>
    <associate|generic|<tuple|3|?>>
    <associate|prop:divdiff|<tuple|20|5>>
    <associate|sec:HG|<tuple|5|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      BurdenFaires

      Bishop/Bridges:1985

      Palmgren

      deBoor

      Alexander

      BurdenFaires

      SuliMayers

      Taylor

      CViet

      banach-algebra

      BridgerStolzenberg

      DiffFields
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Main
      result> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Generic zeros
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Polynomials>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Intermezzo: defining
      differentiation <with|font|<quote|roman>|\V> unfinished
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1.5fn>|3.2<space|2spc>Iterated integrals.
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Hermite-Genocchi
      formula> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Conclusion>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Acknowledgements>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>