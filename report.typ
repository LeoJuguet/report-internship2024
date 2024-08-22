// Setup
#import "@preview/ansi-render:0.6.1": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/cetz:0.2.2"
#import fletcher.shapes: diamond
#set page(numbering: "1")

#let head(title, authors, date) = align(center)[
  #text(17pt)[*#title*]\
  #authors \
  #date \
]

#set heading(numbering:"1.")


#set raw(syntaxes: "jasmin.sublime-syntax")

#show raw.where(block: true) : block.with(
  fill : luma(240),
  inset : 10pt,
  stroke : black,
)

#let def_counter = counter("definition")

#let def(title,text) = block(
  fill: luma(240),
  stroke: green,
  radius : 2pt,
  inset: 1em,
  width: 100%,
  )[
    #def_counter.step()
    *Definition #context def_counter.display(): #title * \
    #text
  ]

// Defined some symbols

#let widen = math.triangle.stroked.t
#let join = math.union
#let meet = math.sect

#let Init = (
  init : "INIT",
  inot : "NOT_INIT",
  maybe : "MAYBE_INIT",
)


#let maybe_eq = math.tilde.eq
#let maybe_le = math.lt.tilde
#let maybe_ge = math.gt.tilde

#let eq = math.eq
#let le = math.lt.eq
#let ge = math.gt.eq

#let len = "len"

#let semOf(expr, isabstract: true, name ) = [
  #let abstrcat = if isabstract {
  	math.hash
  } else {
  	""
  }
  
  #text(red)[$name^abstrcat [|$]$expr$#text(red)[$|]$]
  
  ]

#let semExpr(expr, isabstract : false) = semOf(expr, isabstract: isabstract, $EE$) 
#let semStmt(stmt, isabstract : false) = semOf(stmt, isabstract: isabstract, $SS$)
#let semCond(cond, isabstract : false) = semOf(cond, isabstract: isabstract, $CC$)


#let semExprA(expr, isabstract : true) = semOf(expr, isabstract: isabstract, $EE$) 
#let semStmtA(stmt, isabstract : true) = semOf(stmt, isabstract: isabstract, $SS$)
#let semCondA(cond, isabstract : true) = semOf(cond, isabstract: isabstract, $CC$)

// Truc
#let title = [
  Jasa : The new Jasmin Safety Analyser write with MOPSA
]

#set text(11pt)

#set page(
  header: [
  #align(
    right + horizon,
    title 
  )
  //#line(length: 100%)
  ],
)

#head(title, "Juguet Léo", "March - Jully 2024")

#align(center)[
  #set par(justify:false)
  *Abstract* \

  We have written a new safety checker for Jasmin, a programming language for high-assurance and high-speed 
  cryptographic code implementation. The safety checker detects initialization of scalars, initialization of 
  arrays to a certain extent, and access out of bounds without unrolling loops using widening. This new safety 
  checker is mostly based on the MOPSA library. This new safety checker is undoubtedly faster than the previous one.
  This new safety checker, created with MOPSA, also opens up the possibility to check more properties than the previous 
  safety checker, with the ability to analyze the values.
]


= Introduction <intro>


Jasmin @jasmin is a programming language that aims to be secure, particularly for cryptographic code.
The compiler is written in Coq and provides a proof that the code will be correctly translated to assembly, under certain assumptions.
These assumptions are checked by a static analyzer, but the previous one was too slow.
The goal of this internship was to create a new, more efficient static analyzer that would be able to check that the conditions on a Jasmin code are well-present.

For this, I used MOPSA, a static analyzer library that aims to be modular, in order to easily add a frontend for the Jasmin language.

= Context

Writing a secure program is hard, there are many considerations to take care of, such as ensuring that a variable 
is well-defined and that there are no out-of-bounds accesses.

In Jasmin, a safety analyzer already exists, but there is a main problems:
The current implementation is to slow for big programs.

The main goal of this internship was to explore MOPSA to see if it could be used to replace the old safety checker.

== Contribution

During this internship, I wrote a brand new safety analyzer for Jasmin @jasmin using the MOPSA @mopsa-phd library. 
This safety checker is modular, meaning that a function can be analyzed independently. It can check if scalars are 
properly initialized, as well as arrays and memory, and ensure there are no out-of-bounds accesses.

The safety checker uses contracts to check properties and offers a modular analyzer. It is also faster than the previous one.

#outline(indent : auto)


= Jasmin

Jasmin is a programming language for writing high-assurance and high-speed cryptography code. 
The compiler is mostly written and verified in Coq, and except for the parser, the other code written in OCaml is also verified in Coq @jasmin.
Jasmin has some tools to translate a Jasmin program to EasyCrypt or CryptoLine to allow developers to prove that their code is correct. 
However, this translation and the compilation are correct only if the safety properties are verified.
The safety properties are checked by a safety checker. However, the current safety checker is too slow if we want to 
analyze a significant program.

Jasmin has a low-level approach, with a syntax that is a mix between assembly, C, and Rust. Jasmin has 3 types:

- bool for boolean
- inline integers that are not saved somewhere but directly written in the source code when the compiler unrolls the loop
- words of size with the size in ${8,16,32,64,128,256}$
- arrays of words of fixed length at compile time
- pointers that point to a memory space

The user has to specify if a variable has to be in a register or on the stack. But this will not affect the static analysis.

A Jasmin program is a collection of:

- parameters (that are removed right after the parsing)
- global variables (that are immutable)
- functions (they can't be recursive)

The control flow of a Jasmin program is simple, with blocks, if statements, for loops, and while loops, all of which have a classic semantic of an imperative language.

== Safety

#def("Safety properties")[
The safety properties of a Jasmin program are :
- all scalar arguments are well initialized
- all return scalars are well initialized
- there is no out-of-bounds access for arrays
- there is no division by zero
]

In the following report, we will not talk about division by zero, even if a prototype of division by zero detection is implemented, 
because Jasmin is focused on cryptography code, and in particular constant-time programs. Division operations are not used 
because they are not constant-time operatorsa.
= Overview of Abstract Interpretation <abstract-interpretation>

> *Note* : this part and @overview-mopsa are mostly a resume of @mopsa-phd, it only resume for the comprehension and small details to fit
with Jasmin. For proof and more details, please refer to this document.

Abstract interpretation is a technique in the field of static analysis of programs. It analyzes a program by an upper approximation way, 
without having to execute the program.

Abstract interpretation was formalized by Patrick Cousot and Radhia Cousot @cousot-lattice. All concrete values are replaced by an abstract 
value, such that all possible values in a normal execution are included in the concretization of the abstract value.


#def("Poset")[
  A poset or partial order set is a couple $(X, subset.sq)$ with $X$ a set and $subset.sq in X times X$ a relation reflexive,
  anti-symmetric and transitive
]

#def("Sound abstraction")[
  Let $A$ be a set $(C,subset.eq)$ a poset, and $gamma in A -> C$ the concretisation function. 
  $a$ is a sound abstraction of $c$ if $c subset.eq gamma(a)$
]


#grid(
columns: (30%,70%),
[
```jasmin
fn f(reg u64 x)
{
  reg u64 a;

  if x > 0 {
    a = 5;
  }else{
    a = 7;
  }
}
```]
,
[
#text(10pt)[
#figure(
  
  [#diagram(
    node-stroke: 1pt,
    node((0.5,0), [$ a = Init.inot, x = Init.init$], name: <init>),
    edge("-|>",[then]),
    node((0,1), [$ a = Init.init, x = Init.init, x > 0$], name: <then>),
    node((1,1), [$ a = Init.init, x = Init.init, x <= 0$], name: <else>),
    edge(<init>,<else>,"-|>" ,[else]),
    node((0.5,2), [$ a = Init.init, x = Init.init$], name:<end>),
    edge(<then>,<end>,"-|>" ),
    edge(<else>,<end>,"-|>" ),
    node((0.5,1.5),$join$,stroke : none),
  )],
  )<hass-diagram-init>
]]
)
#def("Sound abstraction")[
  Let $A$ be a set $(C,subset.eq)$ a poset, and $gamma in A -> C$ the concretisation function. 
  $a$ is a sound abstraction of $c$ if $c subset.eq gamma(a)$
]

Intuitively, the abstraction calculates an overbound of the real possible values. The abstraction 
is correct even if it detects a bug that didn't exist, but it is incorrect if it fails to detect a bug that does exist.

#def("Sound abstraction operator")[
  Let $A$ be a set $(C,subset.eq)$ a poset, and $gamma in A -> C$ the concretisation function. 
  $f^hash in A -> A$ is a sound abstraction of $f in C -> C$ if
  $forall a in A, f(gamma(a)) subset.eq gamma(f^hash (a))$
]


== Widening <widening>

The widening operator was initially introduced in a Cousot's Cousot's paper @cousot-lattice. 
The widening operator was defined to find a fixpoint in the approximation of while loops, like it's
impossible to compute the fixpoint of all loops with the guaratee that this calcul terminate. 
The semantic of while loop is given in @sem-stat.

#def("widening")[
  A binary operator $widen$ is defined by
  - $widen : A times A -> A$
  - $forall (C,C') in A^2, C <= C widen C', C' <= C widen C'$
  - $forall (y_i)_(i in NN) in A$, the sequence $(x_i)_(i in NN)$ computed as $x_0 = y_0, x_(i+1) = x_i widen y_(i+1)$,$exists k >= 0 : x_(k+1) = x_k$ 
  
]

The 3rd condition of the widening operator is important to guarantee that the analysis will finish, but this does not 
permit us to conclude that the loop can finish, unless the index used in the loop is bounded.


= Overview of MOPSA <overview-mopsa>

MOPSA, which stands for Modular Open Platform for Static Analysis, is a research project 
that develops a tool in OCaml of the same name. The goal is to create static analyzers based
on abstract domains modularity.


(* TODO: Insert an image to represent MOPSA *)

In MOPSA, to register a new abstraction, the developer only needs to register a Domain.

MOPSA performs an induction on the syntax.

MOPSA offers different domains that are already implemented for a universal language, and these domains can be easily used by another target language.

To have a correct abstract interpretation with MOPSA, we only need to provide a domain of the appropriate form.

#def("Value abstract domain")[
  A value abstract domain is :
  - a poset $(D^hash, subset.sq.eq\ ^hash)$
  - a smallest element $bot$ and a largest element $top$
  - a sound abstraction of :
    - constant and intervals 
    - binary operators
    - set union and intersection
  - a widening operator $widen$
  - a concretisation operator $gamma : D^hash -> P(ZZ)$
]



== Semantic of statements <sem-stat>

=== Semantic of Jasmin
We write $semExpr(e) : S -> P(ZZ)$ the semantic of an expression e.
Variables are evaluate in a context $sigma$. 

$
  semExpr(v)sigma = { sigma(v) }\
  semExpr(z in ZZ)sigma = {z} \
  semExpr(e_1 smash e_2) = semExpr(e_1) smash semExpr(e_2) \
$


We write $semStmt(s) : S -> P(S)$ the semantic of an expression $s$.
And we defined a conditional operator $semCond(c) : P(S) -> P(S)$, that filter the state that can statify the condition
$c$.

$
  semCond( e_1 square e_2)Sigma = { sigma in Sigma | exists v_1 in semExpr(e_1)sigma, exists v_2 in semExpr(e_2)sigma, v_1 square v_2 }  
$ 

$
  semStmt(s_1\; ...\;  s_n) = semStmt(s_n) circle ... circle semStmt(s_1) \
  semStmt("if" c {s_t} "else" {s_f}) = semStmt(s_t) circle semCond(c) join semStmt(s_f) circle semCond(not c) \
  semStmt( x = e)Sigma = {sigma[x <- v] | sigma in Sigma, v in semExpr(e)sigma} \
  semStmt("for" v = c_1 "to" c_2 { s }) = semStmt(v = c_1\; "while" v < s { s; v = v + 1;}) \
  semStmt("while" c { s_1 } (s_2)) = semStmt( s_2 \; "while" c { s_1 \; s_2 } ) \
  semStmt("while" c { s_1 })Sigma = semCond(not c) ( union.big_(n in NN) (semStmt(s) circle.small semCond(c))^n Sigma)
$
In Jasmin, a function only have one `return` statement, at the end of the function.

=== Semantic of Jasmin Abstraction
Like it's not possible to calculate the exact semantic of jasmin, we calculate an overapproximation of states.
$
  semStmtA(s_1\; ...\;  s_n) = semStmtA(s_n) circle ... circle semStmtA(s_1) \
  semStmtA("if" c {s_t} "else" {s_f}) = semStmtA(s_t) circle semCondA(c) join semStmtA(s_f) circle semCondA(not c) \
  semStmtA( x = e)Sigma = {sigma[x <- v] | sigma in Sigma, v in semExprA(e)sigma} \
  semStmtA("for" v = c_1 "to" c_2 { s }) = semStmtA(v = c_1\; "while" v < s { s; v = v + 1;}) \
  semStmtA("while" c { s_1 } (s_2)) = semStmtA( s_2 \; "while" c { s_1 \; s_2 } ) \
  semStmtA("while" c { s_1 })Sigma = semCondA(not c) lim delta^n (bot) "with" delta(x^hash) = x^hash widen (sigma^hash union.sq^hash semCondA(s) circle.small semCondA(c) x^hash)
$

But calculate all theses states takes to many times, so we abstract them.

These statments are classic in abstract interpration so Mopsa, already have domain that handle theses statments.





== Default Domain


Mopsa offer different default domain :

- numerical domains : in particular interval domains and relational domains.
- iterators domains in universal language to manipulate principal statements.

= Initialisation of scalar

In Jasmin, all scalar arguments or return values of a function have to be initialized.
Moreover, a variable is well-initialized if it is assigned to a well-initialized expression. 
A well-initialized expression is defined according to the following abstract value domain @poset-init-domain.

#figure(
diagram(
  node((0.5,0), [ MAYBE_INIT], name: <maybe>),
  node((0,1), [INIT], name: <init>), 
  node((1,1), [NOT_INIT], name:<not_init>),
  node((0.5,2), [$bot$], name:<bot>),
  edge(<init>,<maybe>, "->"),
  edge(<not_init>,<maybe>, "->"),
  edge(<bot>, <init>, "->"),
  edge(<bot>,<not_init>, "->"),
  spacing: 1em,
),
  caption: "Poset of Init domain"
)<poset-init-domain>

The $bot$ value of this abstraction is never reached, and is only present to have a lattice.
$Init.maybe$ play the role of $top$.


$ 
a meet b = a join b = cases("if" a = Init.init and b = Init.init "then" Init.init, "else" Init.inot)
$
$
  semExpr(a star b) = semExpr(a) union semExpr(b) "whith" star in { + , - , * , \/ , %} \
  semExpr(circle.filled.small a) = semExpr( a )  "whith" circle.filled.small in { + , - } \
  semExpr(c) = Init.init "with" c "a constant" \
$

$
  a meet b = a widen b = a join b = cases(
    a "if" a = b,
    Init.maybe  "if" a != b,
  )
$

$
  semExprA(a star b) = semExprA(a) union semExprA(b) "whith" star in { + , - , * , \/ , %} \
  semExprA(circle.filled.small a) = semExprA( a )  "whith" circle.filled.small in { + , - } \
  semExprA(c) = Init.init "with" c "a constant" \
$

We also add a special instruction `InitVariable(var)` that takes a variable and return the same
context where the variable in argument is now initialized.

Inside abstract interpretation these values can be interpret has :
- $Init.maybe$ there exist a path were the variable can be initialized
- $Init.init$ for all path the variable is initialized
- $Init.inot$ for all path the variable is not initialized

We also defined $gamma(v) = {top_("typeof"(v))} $.

$Init.maybe$ help to continue the analysis without the knowledge that there exist a path were the varible
is initialized.

This is a value abstract domain. So we can implement it in Mopsa and have a correct
abstract interpretation of the initialisation of scalar variables.

= Initialisation of arrays <init-array>

We name a cell initialised if before the cells was assign to a well initialized expression.


== The difficulty <difficulty-array-init>
The principal difficulty to prove that an array is well initialized, is to be sure
that the overapproximation of the index use to set a cell in a loop will not
provided an approximation were at the end all the array is initialized, when it's false
like in the @ex1 were the over approximation will give `a[x] = 5` with $x in [2;512]$, but
only even indexes are initialized.

#figure(
```jasmin
inline int i;
stack u32 a[512];
for i = 0 to 256 {
  a[2*i] = 5;
}
```,
caption: [partial initialisation of an array],
) <ex1>

== Aproach

To initialize an array, different methods exist:

*Expanding the array:* A first approach is to define a variable for each cell of an array. This can work in Jasmin because 
arrays have a fixed size. However, this will be memory-consuming, and there is a risk of slowing down the analysis, because 
the analysis has to iterate over all cells when we do an assignment with an index that has an overapproximation value in the analysis,
and this ask to unroll loops.

*Array smashing:* This approach abstracts a variable by a single variable that represents the entire content of the array, 
but this will not work in your case to prove the initialization.

*Cousot's Cousot's approach:* The approach described in the Cousot's Cousot's paper @cousot-p @cousot-article defines a 
functor that takes 3 different domains to represent values and bounds. The advantage of this algorithm is that it can 
show that an array is initialized even if it is not initialized from one border to the center. However, the problem with 
the implementation described is that the functor takes three domains, and the function deals with values in that domain, 
particularly with some symbolic equalities on the bounds. This way of dealing with domains is not really in the spirit of 
MOPSA, which prefers to deal with domains and have less information about them. The symbolic equalities would require 
reimplementing the relational-domain already available, or to be able to do a symbolic equalities of a variable
in two different context, but this ask to modify Mopsa. 

We want deal with to constraints. First we want avoid to have one variable for
each cells of the arrays. Because create a variable for each cells, means
that each cells has a representation in each abstract domain, like we don't
know who many domains we have the memory needed to represent a simple array
can grow rapidly. Moreover this also means that we need to modify each variable
and check each variable, this can also slow down our safety checker.
Secondly, we want to be able to prove that an array is well initialised without
unrolling loop, because unrolling loop slowdown the analysis, but give a more
precise analysis for loop with invariant difficult to infer, see @perf.


So we finally move to a more simpler algorithm that can only prove the initialization of arrays if
we initialize from border to the center, this initialization is a form of array partitionning but
with a fixed number of partition at 3. In pratices, this is the case in a majority of cases that
jasmin deal.


== 3 Segments <3-array-segs>

=== Representation


#figure(
  [
    #grid(
      columns: (20%,60%,20%),
      stroke: black,
      inset: 1em,
      $s_1$, $s_2$,$s_3$
    )
  ],
  caption : [Representation of an array]
)<repr-array>

We represent each arrays with 3 segments, so only 7 variables are needed to represent an array.
Four variables are to represent the limit of segments, and three are for representing the value in the segment.
So an array $a$ can be represented like that $a = {b_0} s_1 {b_1} s_2 {b_2} s_3 {b_3}$ with the properties $0 <= b_1 <= b_2 <= "len"(a)$.
Moreover $b_0$ and $b_3$ are always constant with repectively the value $0$ and $len(a)$.

Variables never change, whe only reassign variable with new values, this permit to delegate operations,
union, intersection, to other domain were the variable live.

Initially we have : 
$
  b_0 = 0, \
  b_1 = 0, \
  b_2 = b_3, \
  b_3 = "len"(a) \
  e_1 = e_2 = e_3 = top "and not init"
$

This method is pretty simple to implement in mopsa. The only case that you need to deal is when you want get a result or when we want assign a 
value.


=== Setter

#block(
  fill: rgb("#f28585" ),
  width: 100%,
  stroke: red,
  inset: 1em,
)[
  *The intuition*: 
  The representation with 3 segments, has two "movable" bounds $b_1$, $b_2$, in lot
  of cases, the center is not initialized. So the extremities contains more precise information.
  We want avoid to lose it, so we extends the extremities segments to the middle only when we are sure
  that the bounds is always included in the interval set.
]


Let suppose that we do $a[i] = e$ with $i$ and $e$ two expression.
First we suppose that $gamma(semExpr(i)) subset.eq [0; len(a)]$, if this is not the cases,
we raise an out of bound exception and we continue with this assumption.

We have the following cases, if different cases are possible, if there exist in the environment a concretisation
such that the cases is valid, we do all cases separately and we join the different array abstraction obtains.

$

  "if" [i; i + "len"] subset.eq [b_j; b_(j+1)] "then" s_(j+1) = s_(j+1) join e ("with" j in [|0;2|])\
  cases(
    "if" b_1 = i "then" cases(
      "if" i + len <= b_2 "then" b_1 <- i + len and s_1 <- s_1 join e,
      "if" i + len > b_2 "then" b_1 <- i + len and b_2 <- i + len and s_1 <- s_1 join e,
      "if" i + len = b_2 "then" b_1 <- i and b_2 <- i + len and s_2 <- s_1 join e
    ),
    "if" b_1 < i "then" cases(
      "if" i + len < b_2 "then" s_2 <- s_2 join e,
      "if" b_2 = i + len "then" b_2 = i and s_3 <- s_3 join e,
      "if" b_2 < i + len "then" cases(
        "if" b_2 < i "then" s_3 <- s_3 join e,
        "if" b_2 >= i "then" b_2 = i and s_3 <- s_3 join e,
       )
    ),
    "if" i < b_1 "then" cases(
      "if" i + len < b_1 "then" s_1 <- s_1 join e,
      "else" b_1 <- i + len and s_1 <- s_1 join e,  
    )
  )
$

=== Access

To access an element of a table `a[i]` we use a simple algorithm.
We fold from left to right the bounds. If two bounds are *always* equal,
we didn't take the value between them, otherwise if the interval $[|i;i + "len"|]$
overlapp with the interval created by the two bounds, we keep the argument. 
At the end, we doing the union of all segment we keep.

So in maths way we have :
$gamma(a[i]) = join_(j in [|0;2|] and gamma(i) meet gamma([b_j;b_(j+1)]) != emptyset) gamma(s_j) $


=== Example

#block(
stroke: rgb("#C8AD7F"),
fill: rgb("#C8AD7F"),
inset: 5pt,
width: 100%,
[ 
*Example*
#grid(
  columns: (30%,70%),
[
```jasmin
fn f() -> reg u64
{
  reg u64[20] a;
  inline int i;
  reg u64 ret;
  reg bool b;

  b = true;
  i = 0;

  while (b) {
    if i > 10 {
      b = false;
    }
    a[i] = 0;
    
    i += 1;
  }

  ret = a[15];
  return ret;
}
```
],[
  On the example on the right, after that the first loop is executed, we have
  $ a = {0} Init.init {b_1 = 1} Init.inot {b_2 = 21} Init.inot {b_3 = 21}$ and $i = 1$, $b = "true"$,
  before redo a loop iteration, the widening operator is apply, and the numeric domain
  cannot infer that $i <= 10$, will we have the upper approximation $i = [1; + infinity]$,
  and we also have that $i = b_1$.
  
  $ a = {0} Init.init {b_1 = [1, + infinity]} Init.inot {b_2 = 21} Init.inot {b_3 = 21}$ and $i = 1$, $b = "true"$,


  So when we access at the index 15 of the array $a$ we do the join of $s_1$ and $s_2$ so we obtain $Init.maybe$.
]
)
]
)

#block()[
  *Note :*
Here we only talk about initialization of the array, but in fact, with the help of Mopsa, and the separation of domains, 
we also have a range of possible values for each interval.
The only details is that in Jasmin, we can cast an array to array of the same size in byte, 
but with a different type interpretation for values (see a table of u64 to a table of u32 for example), 
in this case for the moment we send $top$ value in numerical domains, to be sure to be sound and avoid to deal with intenger representation.
  ]

=== Soundness


= Contract and function call <contract>

Like in lot of programming language, it's possible in Jasmin to do function call,
but a function call didn't have any side effect, like jasmin program didn't produce any
side effect.
A function call take differents a predefined number of argument and return a tuple
of argument that is imediately split when we do an assign of a function call
this is write like this ```jasmin v1, v2, v3 = f(e1,e2,e3);``` in jasmin.

We name a contract a list of precondition or postcondition that an function has to verify.
Mopsa already have a contract languages for C @contract-paper and it's similar to Frama-C's ACSL but there are
used only if the function source is not available. However in Jasmin's team we want be able to check independently 
each function. So we slightly modify from our side the comportment of contract, by modifing our domain on your side.

The new comportment is :
When we have a function call, we check if we have a contract associated to this function,
if yes we check that the requires are satifies, and we apply the post-condition to the variable $v_i$.
Otherwise if we didn't found any requires we only check that the scalar in argument are well initialized,
and we assign the return value to $top$ and initialized for the case of scalar variable.

Jasmin has an experimental feature of contract to send it to Easycript or Cryptoline, we reuse the syntaxt tree where 
we catch expression of the following form that we can translate to Mopsa stubs.

Supported contract in Jasmin, for this experimentation are :
- Conjonction of proposition
- `init_array(v : var, offset: int, len: int)` a propostion that affirm that the array `v` is well initialized between the indexes `offset` and `int`
- Post and Pre condition

*Remark :* the contract language from user side didn't have a proposition to say that a scalar variable is initialized, because this is a pre and post condition
that have to be check for every function. 

= Memory

#emoji.warning *Warning :* this part is not yet implemented in the safety checker.



The memory model in Jasmin is pretty simple, it can be viewed as a large array.

In the previous safety checker, it was able to infer which regions of an array 
had to be initialized. But this mechanism does not seem useful, and the constraints 
given by the programmer are preferred, to ensure that the programmer knows what they 
are doing. For this, we prefer that the programmer provides a contract @contract through the Jasmin annotation system.

If we assume that each pointer provided by the programmer points to a distinct region 
(there is no overlap between the regions defined by each pointer), we can reuse the 
3-segment implementation that we previously used for arrays @3-array-segs.


The planned contracts for the moment consist of 3 predicates:

- `init_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is readable, so it is an initialized region.
- `write_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is writable.
- `assign_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is initialized, at the output of the function.

To check for out-of-bounds access in memory, i.e., access to places where we cannot write, we can easily check that we are within the 
bounds declared as readable. In Jasmin, the memory is allocated before the call, and generally, there are not many arguments to function calls,
so the number of segments will be finite and not expensive.
To check if we can write to a place, the same check as before can be done.
The complicated part is to check if a region that is not initialized at the function call but is well-initialized at some point during the 
execution of the call or at the end. So, to check the `assign_memory` predicate.
If we assume the strong assumption that each pointer points to a different region of memory without overlapp, then we can consider each pointer as an 
array of length $max_(("offset", len) in P_v)("offset"+len)$ (with $P_v$ the set
of pair offset, length that appear in a predicate relatif to $v$) 
and we can set as initialized the regions that we know are initialized, if they are on one side of the array.

This method, which unfortunately has not been tested in practice, seems to handle a majority of cases. 
The only real problem comes from the inability to handle pointer aliasing.

= Performance and Implementation <perf>

#ansi-render(
  read("example_output"),
  theme: terminal-themes.tango-dark
)

To give an idea of the performance of the new safety checker, we tried it on the `ntt` function @ntt-function.

With the old safety checker, the analysis of the function took `30 seconds`, this is now possible in less than `3 seconds`.
However, in both cases with the widening, we are only able to prove that the array is well-initialized (because it is well-initialized before). 
Due to the upper bound approximation of scalars in the loop for the widening, we are not able to prove that there is no out-of-bounds access.
If we unroll the loop, we are able to prove that the array is well-initialized and there is no out-of-bounds access, 
this takes `45 seconds` with the new safety checker. With the older safety checker, after `3 hours`, the analysis was not finished.
In another file with 6 different functions #footnote([#link("https://github.com/LeoJuguet/jasmin/blob/cryptoline-mopsa/compiler/jasa/tests/test_poly.jazz")]), 
the analysis takes around `0.430s` for the new checker to be analyzed, and around `6.37s` for the previous checker. 
(see @details-performances-test for details about the tests.)


The final implementation for the arrays feature counts around 3,000 lines of code. The previous safety checker that performed more checks has 7,000 lines of code. 
However, around 1,000 lines of code in the new safety checker are for extending the MOPSA AST and translating the Jasmin AST to MOPSA.

= Future

This new safety checker, written with MOPSA, is faster than the previous one, and the way MOPSA is built provides 
some ideas to add more checks inside the safety checker. However, implementing the support of basic memory will be 
necessary to support a larger proportion of Jasmin programs. But without a doubt, it is possible to implement this with MOPSA,
 without significant loss in speed.

It seems that with MOPSA, it is possible to handle more checks on values, such as verifying if an array is initialized with only 0s.

Detection of loop termination will also be interesting to check, but due to the over-approximation approach of MOPSA, 
this may not be easy to implement. Currently, termination is only proved when loops are fully unrolled and the analysis terminates.

Other tasks need to be completed to finish the prototype and move towards a more "production-ready product".

In Jasmin, it is possible to call a CPU instruction and get the result and flags, which depend on the target CPU. 
For now, the output is the top value and initialized for scalar values, but an approach similar to function calls will be possible, with specific cases handled.

Similar things can also be done for system calls, which are not yet handled.


= Conclusion

The new safety checker written with MOPSA is faster than the previous one and offers the possibility of carrying out more checks in the future.
Futhermore, Mopsa's modularity means that the code is more readable, faster and easier to add options to. For the moment, 
the checker correctly checks variable initialisation, array initialisation in most cases and out-of-bounds accesses. 
In addition, it's modular and works using a contract system. But MOPSA, offer after a time of adaptation to understant who
each domains live together a simple and easy way to add more domains for specific analysis.

= Acknowledgements


Thank you to the MPI-SP and the Groupe de Gilles for hosting me during this course.
Thanks to Manuel Barbosa for his supervision and to Benjamin Grégoire, Vincent Laporte and Lionel Blatter 
for following the project and answering questions about Jasmin.
Thanks to Raphael Monat from the MOPSA team for taking the time to answer my questions about abstract interpretation 
and MOPSA and for monitoring the project.




#bibliography("report.bib", full : true, style : "association-for-computing-machinery")


#pagebreak()

#set heading(outlined: false)

= Annexes

== Test unrolling loop <test-speed-unroll-loop>
```jasmin
fn f() -> reg u64
{
  reg u64 a;
  inline int i;

  for i = 0 to 256 {
    a = i;
  }

  return a;
}
```

For this pretty simple function that is safe and have only
two simple scalar variabke, if we unroll the loop, the safety checker take `0.255s`
but if we don't unroll the loop the same analysis take `0.007s`.
So for a function simple like that the difference is important.

== Ntt function <ntt-function>


#raw(read( "ntt.jazz"), block: true, lang: "jasmin")



== Details of performances test <details-performances-test>

The test was executed on a machine with:
- CPU: `AMD Ryzen 7 7840HS w/ Radeon 780M Graphics (16) @ 5.137GHz`
- GPU: `Radeon 780M`
- Memory: `16GB DDR5 5600MHz`
- OS: `Linux`

To test the performance of the new safety checker, we ran the following command in the `compiler` folder of the project:

```bash
time ./jasa.exe -config jasa/share/config_default.jazz file_test.jazz
```

The additional argument `-loop-full-unrolling=true` was added to perform the test with full unrolling.

To test the old safety checker, we ran the following command:

```bash
time jasminc -checksafety file_test.jazz
```

Before running this test, we verified that all functions were marked for export.

To test unrolling with the old safety checker, we generated a config file with `-safetymakeconfigdoc` and 
modified the `k_unroll` argument to `10000`, which simulates a large amount of loop unrolling.
