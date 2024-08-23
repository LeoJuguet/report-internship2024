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
  fill: rgb("#edFCe6"),
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

#let widen = math.gradient
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

#let semOf(expr, isabstract: true, domain : "",name ) = [
  #let abstrcat = if isabstract {
  	math.hash
  } else {
  	""
  }
  
  #text(red)[$name^abstrcat_domain [|$]$expr$#text(red)[$|]$]
  
  ]

#let semExpr(expr, isabstract : false) = semOf(expr, isabstract: isabstract, $EE$) 
#let semStmt(stmt, isabstract : false) = semOf(stmt, isabstract: isabstract, $SS$)
#let semCond(cond, isabstract : false) = semOf(cond, isabstract: isabstract, $CC$)


#let semExprA(expr, isabstract : true,domain : "") = semOf(expr, isabstract: isabstract,domain: domain , $EE$) 
#let semStmtA(stmt, isabstract : true,domain : "") = semOf(stmt, isabstract: isabstract,domain: domain, $SS$)
#let semCondA(cond, isabstract : true,domain : "") = semOf(cond, isabstract: isabstract,domain: domain, $CC$)

// Truc
#let title = [
  Jasa : The new Jasmin Safety Analyser based on MOPSA
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

  We present a new safety checker for Jasmin, a programming language for high-assurance and high-speed 
  cryptographic code implementation. The safety checker detects initialization of scalars, initialization of 
  arrays to a certain extent, and access out of bounds without unrolling loops using widening. This new safety 
  checker is mostly based on the MOPSA library. It is undoubtedly faster than the previous one,
  thanks to the support of function contract and to do modular analysis.
  This new safety checker, created with MOPSA, also enables checking more properties than previous 
  safety checker, with the ability to analyze the values.
]


= Introduction <intro>


Jasmin @jasmin is a programming language that aims to be secure, particularly for cryptographic code.
Its compiler is written in Coq and provides a proof that the code will be correctly translated to assembly, under certain assumptions.
These assumptions are checked by a safety checker, but the previous one was too slow, and not as precise as we wanted. Moreover
the safety checker is hard to maintain today, and doesn't allow modular analysis.
The goal of this internship was to create a new, more efficient, more maintanable, and more precise
 safety analyzer that would be able to check that the conditions on any Jasmin code is verified.

For this task, I used MOPSA, a static analyzer library that aims to be modular, in order to easily add a frontend for the Jasmin language.
By relying on the third-party library MOPSA, which maintains the backend of the abstract interpretation, the resulting codebase is more maintainable.

= Context


Writing a secure program is hard, as there are many considerations to take into account, and often small mistakes are 
involuntarily made by programmers, such as badly definining variables or accessing out-of-bound memory. These mistakes 
can lead to writing at unsafe locations, leading to an information leak. Hence, a tool is needed to detect mistakes.

In Jasmin, a safety analyzer already exists, but there is a main problem:
The current implementation is too slow for big programs, it's impossible to run an analysis on an independent function without
inlining other functions.
Moreover the safety checker also asks to maintain a backend to be able to do abstract interpretation.

The main goal of this internship was to explore MOPSA to see if it could be used to replace the old safety checker.

== Contribution

During this internship, I wrote a brand new safety analyzer for Jasmin @jasmin using the MOPSA @mopsa-phd library. 
This safety checker is modular, meaning that functions can be analyzed independently. It can check if scalars are 
properly initialized, as well as arrays and memory, and ensure there are no out-of-bounds accesses.

The safety checker uses contracts to check properties and offers a modular analyzer. It is also faster than the previous one.

#outline(indent : auto)


= Jasmin

Jasmin is a programming language for writing high-assurance and high-speed cryptography code. 
The compiler is mostly written and verified in Coq, and except for the parser, the other code written in OCaml is also verified in Coq @jasmin.
Jasmin has some tools to translate a Jasmin program to EasyCrypt or CryptoLine to allow developers to prove that their code is correct. 
However, this translation and the compilation are correct only if the safety properties are verified.
The safety properties are checked by a safety checker.

Jasmin has a low-level approach, with a syntax that is a mix between assembly, C, and Rust. Jasmin has 3 types:

- bool for boolean
- inline integers that are not saved somewhere but directly written in the source code when the compiler unrolls the loop
- words of size with the size in ${8,16,32,64,128,256}$
- arrays of words of fixed length at compile time
- reg variables that can hold addresses

The user has to specify if a variable has to be in a register or on the stack. But this will not affect the safety analysis.

A Jasmin program is a collection of:

- parameters (that are removed right after the parsing)
- global variables (that are immutable)
- functions (they can't be recursive)

The control flow of a Jasmin program is simple, with blocks, if statements, for loops, and while loops, all of which have a classic semantic of an imperative language.

== Safety

In Jasmin, safety is formally defined as "having a well-defined semantics", as specified in Coq. 
A function is deemed safe if it can reach a final memory state and result values such that executing 
the function from the initial state successfully terminates in that final state. The properties that must be verified include the following:


#def("Safety properties")[
The safety properties of a Jasmin program are :
- all scalar arguments are well initialized
- all return scalars are well initialized
- there is no out-of-bounds access for arrays
- there is no division by zero
- termination
- alignment of memory access
]

Out-of-bounds access is a common condition in software verification, as it helps prevent writing to unauthorized memory locations and avoids information leaks. 
Checking for division by zero is also crucial to ensure that the program does not crash. Memory access alignment is required by certain architectures and 
can enhance execution speed.

Termination is important, especially in cryptographic programs, as most of them need to execute in constant time. Scalars must be initialized to ensure 
that they are properly represented in the generated assembly code.



In the following report, we will not talk about division by zero, even if a prototype of division by zero detection is implemented, 
because Jasmin is focused on cryptography code, and in particular constant-time programs. Division operations are not used 
because they are not constant-time operator.
We will focus on the initialization of scalars and arrays, as well as out-of-bounds access to arrays

= Overview of Abstract Interpretation <abstract-interpretation>

> *Note* : this part and @overview-mopsa are mostly a summary of @mopsa-phd. For proof and more details, please refer to this document.

Abstract interpretation is a technique in the field of static analysis of programs. It analyzes a program by an upper approximation way, 
without having to execute the program.

Abstract interpretation was formalized by Patrick Cousot and Radhia Cousot @cousot-lattice. All concrete values are replaced by an abstract 
value, such that all possible values in a normal execution are included in the concretization of the abstract value.


A perfect abstract interpretation would calculate the exact set of possible states of a program during or at the end of the interpretation. 
However, it is generally impossible to calculate such a set. Therefore, we compute an approximation. To do this, we define a poset over the set 
of possible states of a program, and we say that the abstraction is sound, meaning it is a correct approximation, if it is possible to derive an 
upper set of possible states of the program from the abstraction.

#def("Poset")[
  A poset or partial order set is a couple $(X, subset.sq)$ with $X$ a set and $subset.sq in X times X$ a relation reflexive,
  anti-symmetric and transitive
]



#def("Sound abstraction")[
  Let $A$ be a set $(C,subset.eq)$ a poset, and $gamma in A -> C$ the concretisation function. 
  $a$ is a sound abstraction of $c$ if $c subset.eq gamma(a)$
]

Intuitively, the abstraction calculates an overbound of the real possible values. The abstraction 
is correct even if it detects a bug that didn't exist, but it is incorrect if it fails to detect a bug that does exist.

The notion of sound abstraction can also be extends to function.

#def("Sound abstraction operator")[
  Let $A$ be a set $(C,subset.eq)$ a poset, and $gamma in A -> C$ the concretisation function. 
  $f^hash in A -> A$ is a sound abstraction of $f in C -> C$ if
  $forall a in A, f(gamma(a)) subset.eq gamma(f^hash (a))$
]



#figure([
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
    node((0.5,0), [$ a = top, x = top$], name: <init>),
    edge("-|>",[then]),
    node((0,1), [$ a = 5, x  > 0$], name: <then>),
    node((1,1), [$ a = 7, x  <= 0$], name: <else>),
    edge(<init>,<else>,"-|>" ,[else]),
    node((0.5,2), [$ a = [5;7], x = top$], name:<end>),
    edge(<then>,<end>,"-|>" ),
    edge(<else>,<end>,"-|>" ),
    node((0.5,1.5),$join$,stroke : none),
  )],
  )<hass-diagram-init>
]]
)],
caption: [ Example of abstraction of a program]
)<example-abstraction>

For example in @example-abstraction, first we abstract $a$ and $x$ by $top$ value, that represent the full range of possible values,
when we execute the `then` branch we have the approximation that $x > 0$ and that $a = 5$, but in the `else` branch we have that $x <= 0$ and $a = 7$.
At the end we join the two branch, to limit the number of different abstract state that we have, and the approximation give tha $a$ is in $[5;7]$ and $x$ can
take all values. This is an overapproximation because $a = 6$ is impossible with the code of the example.

For example, in @example-abstraction, we first abstract $a$ and $x$ with the $top$ value, 
which represents the full range of possible values. When we execute the `then` branch, we have the approximation that 
$x > 0$ and $a = 5$. However, in the `else` branch, we have $x <= 0$ and $a = 7$.

At the end, we join the two branches to limit the number of different abstract states we have, 
and the approximation gives that $a$ is in the range $[5; 7]$ while $x$ can take all values. 
This is an overapproximation of the possible states, because $a = 6$ is impossible with the code in the example.



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



MOPSA work with Domain, named composable abstract domain in @mopsa-phd.
These domains handle an abstract representation of the things they want to abstract 
(e.g. an interval of values, or the initialization states). 
These domains also take partial expression and statement transfer functions, which indicate how certain instructions 
modify the abstract representation (e.g. `a = a + 2` has the effect of adding 2 to the interval representation of `a`).
#def("Composable abstract domain")[
  A value abstract domain is :
  - an abstract poset $(D^hash, subset.sq.eq\ ^hash)$
  - a smallest element $bot$ and a largest element $top$
  - Sound abstractions of set union and intersection $union.sq.big^hash, meet.big.sq^hash$
  - a widening operator $widen$
  - a partial expression and statement transfer functions, operating on the global abstraction 
    state $Sigma^hash$. $semExprA("expr" in Epsilon,domain: D^hash)$, $semStmtA("stmt" in S, domain: D^hash)$
  - Concrete input and output states of the abstract domain, written $D^"in"$ and $D^"out"$
  - a concretisation operator $gamma : D^hash -> P(P(D^"in") times P(D^"out"))$
]


In a configuration file, the programmer defines how different domains coexist. 
When composing a domain, the system takes the first domain that can handle a given expression or statement.

The @figure-mopsa-domains illustrates a simplified configuration. 
The red domains are defined specifically for Jasmin. The blue domains are defined by Mopsa for his universal language. 
Some domains only translate Jasmin statements into equivalent 
statements in the universal language offered by Mopsa, like the loop domain that translates Jasmin's while and 
for loops into a while loop of the universal language.

Other domains, like array initialization, provide a special abstraction for Jasmin, in this case to handle 
the initialization of arrays (@init-array). In this simple example, the system first tries to see if the 
intraproc domain from the Jasmin frontend can handle the current expression or statement. If so, that domain 
will handle the case. Otherwise, the system checks the following domains.

Some cases will try to execute two different domains, like array out-of-bounds and array initialization, 
where one domain checks for out-of-bounds access and the other checks and modifies the abstraction to determine 
if an array is properly initialized. A domain can call other domains.
For example, if we have `a = b[i]`, the domains that handle integer assignments will ask for the value of the 
expression `b[i]`, and the same mechanism described before will be used to find the right domains (`array init` to have the value and
`array out of bounds` to check that there is no error).


#figure(
  [
   #diagram(
    node-stroke: 1pt,
    spacing: 1em,
    node((0,0),text(red)[jasmin],stroke: 0pt),
    node((0.5,0),"intraproc", name:<intraproc>),
    node((0.5,1),"interproc", name:<interproc>),
    node((0.5,2),"loop", name:<loop>),
    node((0,3),"array out-of-bounds", name:<arr-out>),
    node((1,3),"array initialization", name:<arr-init>),
    node((0,5),text(blue)[Universal],stroke: 0pt),
    node((0.5,5),"intraproc", name:<intraproc-mopsa>),
    node((0.5,6),"loop", name:<loop-mopsa>),
    edge(<intraproc>,<interproc>, "-|>"),
    edge(<interproc>,<loop>, "-|>"),
    edge(<loop>,<arr-out>, "-|>"),
    edge(<loop>,<arr-init>, "-|>"),
    edge(<arr-init>,<intraproc-mopsa>, "-|>"),
    edge(<arr-out>,<intraproc-mopsa>, "-|>"),
    edge(<intraproc-mopsa>,<loop-mopsa>, "-|>"),
    {
      let tint(c) = (stroke: c, fill: rgb(..c.components().slice(0,3), 5%), inset: 10pt)
      node(enclose: ((-1.5,-0.5),(1,3) ), ..tint(red))
      node(enclose: ((0,5),(1.5,6.5) ), ..tint(blue))
    },
  ) 
  ],
  caption: "Simplified domain configuration"
)<figure-mopsa-domains>


This way of handling abstraction offers a simple method for developers to add abstractions. 
The developer only needs to extend the AST of MOPSA to translate their language into the MOPSA AST, 
which is straightforward with OCaml's extensible types. After that, the developer simply defines new domains 
to handle the new AST cases they have added. Moreover, MOPSA also provides the possibility to use a reduced 
domain to avoid requiring the developer to redo things that are already well-defined, such as the `Value Abstract Domain`, 
which allows for not having to reimplement a full domain. This Value Abstract Domain was used to analyze the initialization of 
scalar variables (@section-init-scalar).

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
  semExpr(e_1 smash e_2) = semExpr(e_1) smash semExpr(e_2) "with" smash in {+,-,times,div,%}\
$
With $A smash B = {x smash y | x in A, y in B} "for" smash in {+,-,times}$ and
$A smash B = {x smash y | x in A, y in B, y != 0} "for" smash in {div,%}$

We write $semStmt(s) : S -> P(S)$ the semantic of an expression $s$.
And we defined a conditional operator $semCond(c) : P(S) -> P(S)$, that filter the state that can statify the condition
$c$.

$
  semCond( e_1 square e_2)Sigma = { sigma in Sigma | exists v_1 in semExpr(e_1)sigma, exists v_2 in semExpr(e_2)sigma, v_1 square v_2 }  
$ 

$
  semStmt(s_1\; ...\;  s_n) = semStmt(s_n) compose ... compose semStmt(s_1) \
  semStmt("if" c {s_t} "else" {s_f}) = semStmt(s_t) compose semCond(c) join semStmt(s_f) compose semCond(not c) \
  semStmt( x = e)Sigma = {sigma[x <- v] | sigma in Sigma, v in semExpr(e)sigma} \
  semStmt("for" v = c_1 "to" c_2 { s }) = semStmt(v = c_1\; "while" v < s { s; v = v + 1;}) \
  semStmt("while" c { s_1 } (s_2)) = semStmt( s_2 \; "while" c { s_1 \; s_2 } ) \
  semStmt("while" c { s_1 })Sigma = semCond(not c) ( union.big_(n in NN) (semStmt(s) compose semCond(c))^n Sigma)
$
In Jasmin, a function only have one `return` statement, at the end of the function.

=== Semantic of Jasmin Abstraction
Because it's not possible to calculate the exact semantic of jasmin, we calculate an overapproximation of states.
In particular for while loops, we didn't try to calculate the fixpoint of each possible iteration, but we use the 
widening operator (defined in @widening), we add a $hash$ in exponent to mark that the calcul is in the abstraction.

$
  semStmtA(s_1\; ...\;  s_n) = semStmtA(s_n) compose ... compose semStmtA(s_1) \
  semStmtA("if" c {s_t} "else" {s_f}) = semStmtA(s_t) compose semCondA(c) join semStmtA(s_f) compose semCondA(not c) \
  semStmtA( x = e)Sigma = {sigma[x <- v] | sigma in Sigma, v in semExprA(e)sigma} \
  semStmtA("for" v = c_1 "to" c_2 { s }) = semStmtA(v = c_1\; "while" v < s { s; v = v + 1;}) \
  semStmtA("while" c { s_1 } (s_2)) = semStmtA( s_2 \; "while" c { s_1 \; s_2 } ) \
  semStmtA("while" c { s_1 })sigma^hash = semCondA(not c) lim delta^n (bot) "with" delta(x^hash) = x^hash widen (sigma^hash union.sq^hash semStmtA(s) compose semCondA(c) x^hash)
$



To have a better approximation of loops, Mopsa, always unrolls the first iteration of the loop.
For loops, if the user has the guarantee that the loops terminate, it is also possible to unroll 
the loop to have a better approximation. However, this slows down the analysis, because each iteration 
of the loop is simulated and there is no guarantee that the analysis will terminate.
The user can also choose to unroll only a fixed number of iterations, and then perform the widening 
operation afterwards. This also provides a better approximation, but it slows down the analysis.

The semantics of these statements and instructions are classic in abstract interpretation, so Mopsa already has domains 
for its universal language that can be reused. The Jasmin expressions and statements can be simply translated to the universal language, 
and this translation is natural without any surprises.




= Initialisation of scalar <section-init-scalar>

In Jasmin, all scalar arguments or return values of a function have to be initialized.
Moreover, a variable is well-initialized if it is assigned to a well-initialized expression. 
A well-initialized expression is defined according to the @concrete-semantic-init.


#figure(
[
$
  semExpr(a star b) = cases("if" semExpr(a) = Init.init and semExpr(b) = Init.init "then" Init.init, "else" Init.inot) "whith" star in { + , - , * , \/ , %} \
  semExpr(circle.filled.small a) = semExpr( a )  "whith" circle.filled.small in { + , - } \
  semExpr(c) = Init.init "with" c "a constant" \
  semStmt( v = e)Sigma = { sigma{ v <- i} | sigma in Sigma, i in semExpr(e)sigma}
$]
, caption: "concrete semantic of variable initialization"
)<concrete-semantic-init>

We defined a slighty modify value abstract domain, where we add a $Init.maybe$ value, to be able to have a more precise abstraction.

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
#let init_domain = "Init"
#figure(
[
$
  a meet^hash b = a widen^hash b = a join^hash b = cases(
    a "if" a = b,
    Init.maybe  "if" a != b,
  )
$
$
  semExprA(a star b, domain: #init_domain) = semExprA(a, domain: #init_domain) union^hash semExprA(b, domain: #init_domain) "whith" star in { + , - , * , \/ , %} \
  semExprA(circle.filled.small a, domain: #init_domain) = semExprA( a, domain: #init_domain )  "whith" circle.filled.small in { + , - } \
  semExprA(c, domain: #init_domain) = Init.init "with" c "a constant" \
$],
caption: "Abstract semantic of variable initialization"
)
We also add a special instruction `InitVariable(var)` that takes a variable and return the same
context where the variable in argument is now initialized.

Inside abstract interpretation these values can be interpret has :
- $Init.maybe$ there exist a path were the variable can be initialized
- $Init.init$ for all path the variable is initialized
- $Init.inot$ for all path the variable is not initialized

We also defined the concretization function to numerical value $gamma_(#init_domain -> "num")$ such that $gamma_(#init_domain -> "num") (v) = {top_("typeof"(v))} $
and to `Init` concrete domain $gamma_(#init_domain -> "concrete init") (v) = cases( { Init.init } "if" v = Init.init, { Init.inot } "if" v = Init.inot, {Init.init, Init.inot} "if" v = Init.maybe)$.


This is a value abstract domain. So by the property 2.5 of @mopsa-phd, MOPSA built a
non-relationnal abstract semantics, that is a sound abstraction of the concrete semantics.

= Initialisation of arrays <init-array>

Determining which parts of an array are initialized is essential for validating functions that access arrays

== The difficulty <difficulty-array-init>
The main difficulty in proving that an array is well-initialized lies in ensuring that the over-approximation 
of the index used to set a cell in a loop does not lead to a situation where it falsely appears that the entire 
array is initialized. For example, in @ex1, the over-approximation might suggest that `a[x] = 5` for `x` $in [2; 512]$, 
while in reality, only the even indexes are initialized

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

== Aproaches

To initialize an array, different methods exist:

*Expanding the array:* A first approach is to define a variable for each cell of an array. This can work in Jasmin because 
arrays have a fixed size. However, this will be memory-consuming, and there is a risk of slowing down the analysis, because 
the analysis has to iterate over all cells when we do an assignment with an index that has an overapproximation value in the analysis,
and this ask to unroll loops.

*Array smashing:* This approach abstracts a variable by a single variable that represents the entire content of the array, 
but this will not work in your case to prove the initialization.

*Parametric segmentation functor:* The approach described in the Cousot's Cousot's paper @cousot-p @cousot-article defines a 
functor that takes 3 different domains to represent values and bounds. The advantage of this algorithm is that it can 
show that an array is initialized even if it is not initialized from one border to the center. However, the problem with 
the implementation described is that the functor takes three domains, and the function deals with values in that domain, 
particularly with some symbolic equalities on the bounds. This way of dealing with domains is not really in the spirit of 
MOPSA, which prefers to deal with domains and have less information about them. 
The symbolic equalities would require reimplementing the relational-domain already available in MOPSA, in order to be able 
to do symbolic equalities of a variable in two different contexts. However, this would ask us to modify MOPSA itself.
We did try to do this, but we finally chose a simpler implementation, for reasons of time and because the simpler algorithm 
covers a sufficiently large number of Jasmin programs.


== 3 Segments <3-array-segs>


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
we initialize from border of the array to the center. In pratices, this is the case in a majority of cases that
jasmin deal.
This initialization is a form of array partitionning but
with a fixed number of partition at 3.


=== Representation

#let arr_domain = "Arr"


We suppose that we have a numerical domain, if possible a relational domain, $D^hash_"num"$ 
and a domain that represents initialization $D^hash_"init"$ 
(a numerical domain can also be used to analyze the values of the array) in the configuration of the analyzer.
We represent each arrays with 3 segments, so only 7 variables are needed to represent an array.
The bounds of segments are represented by variables handled by the $D^hash_"num"$ domain, 
while the values of the segments are represented in the $D^hash_"init"$ domain.
Four variables are to represent the limit of segments, and three are for representing the value in the segment.
So an array $a$ can be represented like that $a = {b_0} s_1 {b_1} s_2 {b_2} s_3 {b_3}$ with the properties $0 <= b_1 <= b_2 <= "len"(a)$.
Moreover $b_0$ and $b_3$ are always constant with repectively the value $0$ and $len(a)$.

Variables never change, whe only reassign variable with new values, this permit to delegate operations,
union, intersection, to other domain were the variable live.

Initially we have : 
$
  b_0 = 0,
  b_1 = 0,
  b_2 = b_3,
  b_3 = "len"(a),
  s_1 = s_2 = s_3 = top "and not init"
$

#figure(
  [
  #box(
    stroke:black,
    inset: 3em,
  )[
    #grid(
      columns: (20%,60%,20%),
      stroke: black,
      inset: 1em,
      $s_1$, $s_2$,$s_3$
    )
    #grid(
      columns: (9%,11%,1%,59%,1%,13%,15%),
      $b_0=0$,$$, $b_1$,$$, $b_2$,$$, $b_3=len(a)$ 
    )]
  ],
  caption : [Representation of an array]
)<repr-array>

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
  The representation with three segments has two "movable" bounds, $b_1$ and $b_2$. 
  In many cases, the center segment is not initialized, meaning that the extremities 
  contain more precise information. To avoid losing this information, we extend the extremity 
  segments toward the middle only when we are certain that the bounds will always be included in the defined interval.
]


Let suppose that we do $a[i] = e$ with $i$ and $e$ two expression.
First we suppose that $gamma(semExpr(i)) subset.eq [0; len(a)]$, if this is not the cases,
we raise an out of bound exception and we continue with this assumption.

We have the following semantics :

#let bound = $compose semCondA(i in [0;len(a)])$

$
    semStmtA(a[i] = e\;) = union.big cases(
    semStmtA(b_1 = i + len\; s_1 = cases(e "if" i = 0,s_1 join^hash e )) compose semCondA(b_1 = i and i + len <= b_2) bound,
    semStmtA(b_1 = i + len \; b_2 = i + len \; s_1 = cases(e "if" i = 0,s_1 join^hash e)) compose semCondA(b_1 = i and i + len > b_2) bound,
    semStmtA(b_1 = i \; b_2 = i + len \; s_2 = e) compose semCondA(b_1 = i + len and i + len = b_2) bound,
    semStmtA(s_2 = s_2 join^hash e) compose semCondA(b_1 < i and i + len < b_2) bound,
    semStmtA(b_2 = i \; s_3 = cases(e "if" i + len = len(a),s_3 join^hash e)) compose semCondA(b_1 < i and b_2 = i + len) bound,
      
    semStmtA(s_3 = s_3 join^hash e) compose semCondA(b_1 < i and b_2 < i + len and b_2 < i) bound,
    semStmtA(b_2 = i \; s_3 = s_3 join^hash e) compose semCondA(b_1 < i and b_2 < i + len and b_2 >= i) bound,
    semStmtA(s_1 = s_1 join^hash e) compose semCondA(i < b_1 and i + len < b_1) bound,
    semStmtA(b_1 = i + len \; s_1 = s_1 join^hash e) compose semCondA(i < b_1 and i + len >= b_1) bound,  
  )
$

In practice, we use a $join^hash$ operation that joins the possible values of two expressions. This is effectively a convex join in the interval domain. 
It's essentially a case disjunction to determine if we can extend the segment on the left or right in the direction of the middle.

When using the numeric relational domain of MOPSA, in the majority of cases, if we initialize from left to right, the first case is the one that is verified, 
even with the widening of bounds and the index in loops.

This simpler approach, while potentially less precise than a full symbolic equality implementation, has proven sufficient for a large number of Jasmin programs, 
allowing us to deliver a working analysis within the given time and resource constraints.

=== Access

To access an element of a table `a[i]` we use a simple algorithm.
We fold from left to right the bounds. If two bounds are *always* equal,
we didn't take the value between them, otherwise if the interval $[|i;i + "len"|]$
overlapp with the interval created by the two bounds, we keep the argument. 
At the end, we doing the union of all segment we keep.

So we have :
$
semExprA(a[i]) = union.big_(j in [|0;2|])^hash (semExprA(s_(i+1)) compose semCondA(b_j <= i <= b_(j+1)))
$


=== Example


In @ex1, with your abstraction, we have the following state before the loop: 
$
a={0} Init.inot{b_1=0} Init.inot{b_2 =len(a)} Init.inot{len(a)}
$
At the end of the first iteration, we have 
$
a={0} Init.init{b_1= 1 = 2i+1} Init.inot{b_2 =len(a)} Init.inot{len(a)} ", with" i=0
$
The widening operator is applied, resulting in $i=[1;255]$. Then, when we execute `a[2*i] = 5`, we find that $2i=[2;510]$.
Thus, we have 
$
a={0} Init.init{b_1 =1} Init.maybe{b_2 =len(a)} Init.inot{len(a)}
$
At the end of the loop, we can only conclude that index 0 is initialized, and possibly some indices between $1$ and $255$.

#block()[
  *Note :*
Here we only discuss the initialization of the array. However, with the help of Mopsa and the separation of domains, we also have a range of 
possible values for each segments. 

The only detail is that in Jasmin, we can cast an array to an array of the same size in bytes, but with a different type interpretation for values 
(see a table of `u64` to a table of `u32`, for example). In this case, for the moment, we send the $top$ value in numerical domains to ensure soundness 
and avoid dealing with integer representation.
  ]

=== Concretization

We define the concretization function as follows: $gamma_#arr_domain (a[i]) = gamma(semExprA(a[i])) $. 
With the $join$ in the setter and getter, we lose some precision, but we are sure that all possible values are represented.
And in practice, this covers the majority of initialization cases.



= Contract and function call <contract>

Like in many programming languages, it is possible in Jasmin to make function calls. 
However, a function call does not have any side effects; that is, a Jasmin program does not produce any side effects. 
A function call takes a predefined number of arguments and returns a tuple of arguments that is immediately unpacked when 
we assign the result of the function call. This is written as follows in Jasmin: 
```jasmin v1, v2, v3 = f(a1,a2, a3,a4);``` 
In this example, we take 4 arguments that return 3 values, but this number is not fixed.


We refer to a contract as a list of preconditions or postconditions that a function must satisfy. 
Mopsa already has a contract language for C (see @contract-paper), which is similar to Frama-C's ACSL, 
but these are used only if the function source is not available. However, in the Jasmin team, we want to be able to 
check each function independently. Therefore, we slightly modified the behavior of contracts by adjusting our domain on your side.

The new behavior is as follows:
When we have a function call, we check if there is a contract associated with this function. If so, we verify that 
the preconditions are satisfied and apply the postconditions to the variables on the left side of the assignment. If we do not find any preconditions, 
we only check that the scalar arguments are well-initialized, and we assign the return value to $top$ and initialize it for the case of scalar variables.

Jasmin has an experimental feature for contracts that allows them to be sent to Easycrypt or Cryptoline. 
We reuse the syntax tree to capture expressions of the following form, which we can translate to Mopsa stubs.

The supported contracts in Jasmin for this experimentation are:

- Conjunction of propositions
- `init_array(v : var, offset: int, len: int)` a proposition that affirms that the array v is well-initialized between the indexes offset and len
- Postconditions and preconditions


*Remark :* 
The contract language from the user side does not have a proposition to indicate that a scalar variable is initialized, as this is a precondition and postcondition 
that must be checked for every function

= Memory

#emoji.warning *Warning:* This part is not yet implemented in the safety checker.

The memory model in Jasmin is quite simple; it can be viewed as a large array.

In the previous safety checker, it was able to infer which regions of an array had to be initialized. However, this mechanism does not seem useful, 
and the constraints provided by the programmer are preferred to ensure that the programmer knows what they are doing. For this reason, we prefer that 
the programmer provides a contract through the Jasmin annotation system.

If we assume that each pointer provided by the programmer points to a distinct region (with no overlap between the regions defined by each pointer), 
we can reuse the 3-segment implementation that we previously used for arrays @3-array-segs.

The planned contracts for the moment consist of three predicates:

- `init_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is readable, indicating that it is an initialized region.
- `write_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is writable.
- `assign_memory(v: var, offset: int, len: int)` defines that the region $[v + "offset"; v + "offset" + "len"]$ is initialized at the output of the function.

To check for out-of-bounds access in memory, i.e., access to locations where we cannot write, we can easily verify that we are within the bounds declared as readable. 
In Jasmin, the memory is allocated before the call, and generally, there are not many arguments to function calls, so the number of segments will be finite and not 
expensive. To check if we can write to a location, the same check as before can be performed.

The complicated part is checking if a region that is not initialized at the function call becomes well-initialized at some point during the execution of the call 
or at the end, to verify the `assign_memory` predicate. If we assume the strong assumption that each pointer points to a different region of 
memory without overlap, we can consider each pointer as an array of length $max_{(("offset", len) in P_v)}("offset" + len)$ (with $P_v$ being the set of pairs 
of offset and length that appear in a predicate related to the variable $v$). We can then set as initialized the regions that we know are initialized if 
they are on one side of the array that abstract $v$.

This method, which unfortunately has not been tested in practice, seems to handle the majority of cases. The only real problem arises from the inability to 
handle pointer aliasing.



= Performance and Implementation <perf>

#figure(
[
#set align(left)

#ansi-render(
  read("example_output"),
  theme: terminal-themes.tango-dark
)],
caption: "Example of output of the safety checker when there is an error or a warning"
)



To give an idea of the performance of the new safety checker, we tested it on the `ntt` function @ntt-function.

With the old safety checker, the analysis of the function took `30 seconds`; this is now possible in less than `3 seconds`.
However, in both cases with the widening, we are only able to prove that the array is well-initialized (because it is well-initialized beforehand). 
Due to the upper bound approximation of scalars in the loop for the widening, we are unable to prove that there is no out-of-bounds access.

If we unroll the loop, we can prove that the array is well-initialized, that there is no out-of-bounds access, and that the loop terminates 
(as the analysis terminates with loop unrolling). This takes `45 seconds` with the new safety checker. With the older safety checker, after `3 hours`, 
the analysis was not finished.

In another file with 6 different functions #footnote([#link("https://github.com/LeoJuguet/jasmin/blob/cryptoline-mopsa/compiler/jasa/tests/test_poly.jazz")]), 
the analysis takes around `0.430 seconds` for the new checker and around `6.37 seconds` for the previous checker. 
(See @details-performances-test for details about the tests.)

The final implementation for the arrays feature consists of around 3,000 lines of code. The previous safety checker, 
which performed more checks, had 7,000 #footnote([calculate with cloc, the code can be found here #link("https://github.com/LeoJuguet/jasmin/blob/cryptoline-mopsa/compiler/jasa/")]) lines of code. However, around 1,000 lines of code in the new safety checker 
are dedicated to extending the MOPSA AST and translating the Jasmin AST to MOPSA.



= Conclusion and future work




This new safety checker, written with MOPSA, checks that scalar variables are well-initialized, 
that array accesses are in bounds, and successfully verifies that arrays are well-initialized when 
they are initialized from one border to the middle. Moreover, the support for contracts allows for independent 
function checks and property verification, such as the initialization of arrays. Furthermore, with the modularity of MOPSA, 
the code is simple to extend and maintain. This implementation is also faster than the previous one, and the way MOPSA is built 
provides ideas for adding more checks inside the safety checker.

However, implementing support for basic memory will be necessary to accommodate a larger proportion of Jasmin programs. 
Without a doubt, it is possible to implement this with MOPSA without significant loss in speed.

It seems that with MOPSA, it is possible to handle more checks on values, such as verifying if an array is initialized with only 0s.

Detecting loop termination will also be interesting to check, but due to the over-approximation approach of MOPSA, 
this may not be easy to implement. Currently, termination is only proven when loops are fully unrolled, and the analysis terminates.

Other tasks need to be completed to finish the prototype and move towards a more "production-ready" product.

In Jasmin, it is possible to call a CPU instruction and get the result and flags, which depend on the target CPU. 
For now, the output is the top value and initialized for scalar values, but an approach similar to function calls will be possible, 
with specific cases handled. Similar functionality can also be implemented for system calls, which are not yet handled.

For a more advanced future, it is also planned to communicate to EasyCrypt which properties have already been proven by the safety checker, 
to establish a workflow where developers run the safety checker and subsequently prove parts in EasyCrypt that have not yet been verified.



= Acknowledgements


Thank you to the MPI-SP and the Gilles's Group for hosting me during this interniship.
Thank you to the Formosa group for their hospitality.
Thanks to Manuel Barbosa for his supervision and to Benjamin Grégoire, Vincent Laporte and Lionel Blatter 
for following the project and answering questions about Jasmin.
Thanks to Raphaël Monat from the MOPSA team for taking the time to answer my questions about abstract interpretation 
and MOPSA and for monitoring the project.

= Meta-Information

- 1.5 months were spent understanding the safety conditions of Jasmin and starting to grasp MOPSA, along with a first implementation to detect division by zero.
- 0.5 months were dedicated to checking for array initialization.
- 0.5 months were spent implementing the initialization of scalar values.
- 1 week was allocated for contracts and function calls.
- 1.5 months were used to understand the segmentation functor and attempt its implementation.
- 2 weeks to implement the final abstraction of arrays.

Some of the time was also spent fixing bugs and attending talks at the institute. 
Additionally, I had the opportunity to participate in two seminars with the Formosa team, 
where I met other team members in person and discussed safety and the future of Jasmin.




#bibliography("report.bib", full : true, style : "association-for-computing-machinery")


#pagebreak()

#set heading(outlined: false)

= Appendix

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

#figure(
[
#raw(read( "ntt.jazz"), block: true, lang: "jasmin")
], caption: [ `ntt` function used for the performance test in @perf,
  the difficulty to prove this function come from nested loop and the difficulty to
  the numerical domain to determine the relation betwen `len`, `start` and `j`, with the
  shift of `len`, so out of bounds
  access is detected without loop unrolling.
] 
)


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



= Mopsa implementation

#figure(
```ocaml
(* Section 3.3.2.2 *)
type ('a, 't) man = {
  get : 'a -> 't;
  set : 't -> 'a -> 'a;

  lattice : 'a lattice;

  exec : stmt -> 'a flow -> 'a post;
  eval : expr -> 'a flow -> 'a eval;

  ask : ('a,'r) query -> 'a flow -> 'r;
  print_expr : 'a flow -> (printer -> expr -> unit);
  get_effects : teffect -> teffect;
  set_effects : teffect -> teffect -> teffect;
}

 (* Section 3.3.2.4 *)
type 'a post = ('a, unit) cases
type 'a eval = ('a, expr) cases

module type DOMAIN =
sig
 (* Section 3.3.2.1 *)
  type t
  val id : t id
  val name : string
  val bottom: t
  val top: t
  val is_bottom: t -> bool
  val subset: t -> t -> bool
  val join: t -> t -> t
  val meet: t -> t -> t
  val widen: 'a ctx -> t -> t -> t

  (* Section 3.3.2.5 *)
  val init : program -> ('a, t) man -> 'a flow -> 'a flow
  val exec : stmt -> ('a, t) man -> 'a flow -> 'a post option
  val eval : expr -> ('a, t) man -> 'a flow -> 'a eval option

  (* Section 3.3.2.6 *)
  val merge: t -> t * effect -> t * effect -> t
  val ask : ('a,'r) query -> ('a, t) man -> 'a flow -> 'r option
  val print_state : printer -> t -> unit
  val print_expr : ('a,t) man -> 'a flow -> printer -> expr -> unit
end
```,
caption: [Domain signature of MOPSA, section comment refer to sections of @mopsa-phd ]
)<domain-mopsa-ocaml>
