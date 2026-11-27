# A Double-Extension Set Theory: Derived Infinity, Arithmetic Strength, and Uniform Models of Zermelo Set Theory

**Zuhair Al-Johar**  
University of Baghdad, Baghdad, Iraq  
*28 November 2026*

## Abstract

We study a first-order double-extension set theory (DEST) with two extensional membership relations. Unrestricted comprehension for formulas in the first relation specifies second extensions. An object defined by comprehension with uniform parameters has equal extensions if it is not a second member of itself. Relational induction yields a uniform least inductive set with uniform members, without an Infinity axiom. DEST and its extension by first-membership set induction are equiconsistent with full second-order arithmetic under Henkin semantics and have the same first-order arithmetic consequences. The upper bound uses a countable back-and-forth construction internal to a powerset-free set theory. Adding uniform subsethood gives an extension consistent relative to ZF, even with first-membership set induction. Uniform subsethood alone suffices over DEST for a hereditarily uniform transitive set whose first-membership structure satisfies Zermelo set theory with full Separation. The accompanying Lean 4 formalization proves the model-existence equivalence conditional on two published reductions, whose use is justified in the paper.

**Keywords:** double-extension set theory, uniformity, second-order arithmetic, relative consistency, Zermelo set theory, formal verification.  
**2020 MSC:** Primary 03E70, 03F25. Secondary 03F35, 03E30, 03B35.

<a id="introduction"></a>

## 1. Introduction

Kisielewicz introduced double-extension set theories, in which each object has two membership extensions ([1](#ref-kisielewicz89), [2](#ref-kisielewicz98)). Holmes showed that two of the early systems are inconsistent ([3](#ref-holmes04)). He also gave an interpretation of ZF in a version with mixed extensionality and a comprehension scheme using a defining formula and its dual ([4, Section 2](#ref-holmes05)).

The variant studied here, which we call DEST, has a separate extensionality axiom for each membership relation. Its comprehension scheme uses formulas in the first membership language with arbitrary parameters to specify second extensions. An object is *uniform* if its two extensions coincide. The uniformity scheme makes a comprehension representative uniform if all parameters are uniform and the representative is not a second member of itself.

We determine the arithmetic strength of this theory and investigate the effect of uniform subsethood. The lower bound uses Friedman’s theorem on parameter-free comprehension ([5](#ref-friedman), [6](#ref-gitman)). For the upper bound, we use the powerset-free set-theoretic interpretation of second-order arithmetic developed by Kanovei and Lyubetsky ([7](#ref-kl), [8](#ref-kl2)), in the tradition described by Simpson ([9](#ref-simpson)). We construct second membership on a domain with inherited first membership by assigning extensions so that the two agree on a prescribed region of the domain. The assignment is a set of the weak metatheory, which allows the verification of induction for formulas involving both membership relations.

Write $B$ for DEST with the axioms in Section [2](#sec:axioms), $T=B+\mathsf{TI}_1$, and $B^+ = B+\mathsf{US}_1$. Let $\mathsf{Z}$ denote Zermelo set theory with Foundation, Infinity and full Separation, but without Choice or Replacement. The principal conclusions are as follows.

<a id="thm:main"></a>

**Theorem 1.1** (Main results).

**(i)** *$B$ proves that there is a least inductive object $w$ such that both $w$ and all its first members are uniform.*

**(ii)** For every first-order arithmetic sentence $\sigma$, with its canonical von Neumann translation $\sigma^*$ into the first membership language,

$$
\mathsf{Z}_2\vdash\sigma\quad\Longleftrightarrow\quad B\vdash\sigma^*
 \quad\Longleftrightarrow\quad T\vdash\sigma^*.
$$

In particular, the external consistency statements are equivalent:

$$
\operatorname{Con}(\mathsf{Z}_2)\;\Longleftrightarrow\;\operatorname{Con}(B)\;\Longleftrightarrow\;\operatorname{Con}(T).
$$

**(iii)** *Externally, $\operatorname{Con}(\mathsf{ZF})\Longrightarrow\operatorname{Con}(B^+ + \mathsf{TI}_1)$.*

**(iv)** *In every model of $B^+$ there is a single hereditarily uniform transitive object $W$ whose first-member structure satisfies $\mathsf{Z}$, including every instance of full Separation.*

For (ii), Friedman’s restriction and the passage to the powerset-free metatheory preserve the number structure, including in nonstandard models. Part (iii) uses finite-fragment models and external compactness. In (iv), satisfaction of Separation is understood for each first-order formula in the ordinary set-theoretic language. Section [9](#sec:lean) identifies the corresponding Lean declarations and their premises.

<a id="sec:axioms"></a>

## 2. Language and axioms

The language $L$ has equality and two binary relation symbols $\in_1,\in_2$. Its first sublanguage $L_1$ contains only equality and $\in_1$. All structures have a nonempty domain. Variables range over the entire domain unless otherwise stated. The following are formula abbreviations, not additional primitive symbols:

$$
\begin{aligned}
\operatorname{U}(a)&\mathrel{:\Longleftrightarrow}\forall x\,(x\in_1a\leftrightarrow x\in_2a),\\
a\subseteq_1b&\mathrel{:\Longleftrightarrow}\forall x\,(x\in_1a\to x\in_1b),\\
\operatorname{Zero}(z)&\mathrel{:\Longleftrightarrow}\forall x\,\neg(x\in_1z),\\
\operatorname{Succ}(a,b)&\mathrel{:\Longleftrightarrow}\forall x\,(x\in_1b\leftrightarrow(x=a\lor x\in_1a)),\\
\operatorname{Ind}(z,t)&\mathrel{:\Longleftrightarrow}z\in_1t\land
 \forall a\,(a\in_1t\to\exists b\,(b\in_1t\land\operatorname{Succ}(a,b))),\\
\operatorname{N}_z(a)&\mathrel{:\Longleftrightarrow}\forall t\,(\operatorname{Ind}(z,t)\to a\in_1t).
\end{aligned}
$$

An object $a$ is *uniform* if $\operatorname{U}(a)$ holds. Note that $\operatorname{N}_z$ is meaningful even in a structure with no inductive object. In that case, it holds for every object. In particular, the induction axiom below does not presuppose Infinity.

<a id="def:base"></a>

**Definition 2.1** (Base theory $B$). The axioms of $B$ are the universal closures of the following formulas and schemes. In comprehension and uniformity, $\varphi(x,\vec p)$ is any $L_1$-formula with free variables among $x,p_1,\ldots,p_k$, where $\vec p=(p_1,\ldots,p_k)$. In induction, $\psi(x,\vec q)$ is any $L$-formula, with arbitrary parameters. In all schemes, variables introduced by the scheme are renamed to avoid capture.

**(B1)** First Extensionality: $\forall a,b\,[(\forall x\,(x\in_1a\leftrightarrow x\in_1b))\to a=b]$.

**(B2)** Second Extensionality: $\forall a,b\,[(\forall x\,(x\in_2a\leftrightarrow x\in_2b))\to a=b]$.

**(B3)** Comprehension:

$$
\exists a\,\forall x\,(x\in_2a\leftrightarrow\varphi(x,\vec p)).
$$

**(B4)** Uniformity:

$$
\begin{aligned}
\Bigl[\,&\bigwedge_{i=1}^{k}\operatorname{U}(p_i)
   \land \forall x\,(x\in_2a\leftrightarrow\varphi(x,\vec p))\\
 &{}\land\neg\varphi(a,\vec p)\Bigr]
 \;\Longrightarrow\;\operatorname{U}(a).
\end{aligned}
$$

The last condition can equivalently be written $a\notin_2 a$ under the preceding extension equivalence. If $k=0$, the empty conjunction is understood to be true, so the uniform-parameter condition is vacuous.

**(B5)** Relational natural-number induction:

$$
\begin{aligned}
\Bigl[\,&\operatorname{Zero}(z)\land\psi(z,\vec q)\\
 &{}\land\forall a,b\,\bigl((\operatorname{N}_z(a)\land\operatorname{Succ}(a,b)\land\psi(a,\vec q))
    \to\psi(b,\vec q)\bigr)\Bigr]\\
 &\Longrightarrow\quad \forall a\,(\operatorname{N}_z(a)\to\psi(a,\vec q)).
\end{aligned}
$$

The variables $a,b,z,t,x$ used as local bound variables are chosen fresh where appropriate. In particular, the comprehension representative $a$ is not a free parameter of the defining formula. Extensionality for $\in_2$ makes the comprehension representative unique. The conditional nature of (B4) is essential: it does not require arbitrary second extensions to agree with first extensions.

For example, let $r$ be the second-extension representative of $x\notin_1 x$. If $r$ were uniform, then $r\in_1r$ would be equivalent to $r\notin_1 r$. Hence $r$ is nonuniform. Since its definition has no parameters, (B4) forces $r\in_2r$, and (B3) then gives $r\notin_1 r$. Adding mixed extensionality to (B1)–(B4) would be inconsistent. Indeed, for any $a$, (B3) gives $b$ whose second extension is the first extension of $a$. Mixed extensionality would force $a=b$, making every object uniform, including $r$.

<a id="def:extensions"></a>

**Definition 2.2** (Extensions of $B$). First-membership uniform subsethood ($\mathsf{US}_1$) is the sentence

$$
\forall a,b\,[(\operatorname{U}(a)\land b\subseteq_1a)\to\operatorname{U}(b)].
$$

First-membership set induction ($\mathsf{TI}_1$) is the scheme

$$
\Bigl[\forall a\,\bigl((\forall x\,(x\in_1a\to\psi(x,\vec q)))
  \to\psi(a,\vec q)\bigr)\Bigr]
 \;\Longrightarrow\;\forall a\,\psi(a,\vec q),
$$

with universal closure, for every $L$-formula $\psi$. No corresponding principle for $\in_2$ is asserted.

Throughout, $\mathsf{Z}_2$ is the first-order, two-sorted theory with number operations $0,S,+,\cdot$, the Peano equations, set extensionality, induction for all two-sorted formulas with parameters, and full comprehension with number and set parameters. This is the customary full-comprehension theory without countable choice ([9](#ref-simpson)). Let $\mathsf{Z}_2^{\mathrm{pf}}$ have the same induction scheme and basic axioms, with comprehension restricted to formulas with no free set variables. Number parameters and bound set quantifiers are permitted.

<a id="sec:infinity"></a>

## 3. Uniform comprehension and derived Infinity

<a id="lem:collection"></a>

**Lemma 3.1** (Uniform collection). Suppose $\varphi(x,\vec p)$ is an $L_1$-formula, each $p_i$ is uniform, and $\forall x(\varphi(x,\vec p)\to\operatorname{U}(x))$. There is a unique uniform object $a$ such that

$$
\forall x\,(x\in_1a\leftrightarrow\varphi(x,\vec p)).
$$

Its second extension is also given by $\varphi$.

*Proof.* By (B3) take $a$ with the specified second extension. If $\neg\operatorname{U}(a)$, (B4) implies $\varphi(a,\vec p)$, whence $\operatorname{U}(a)$ by the hypothesis on the values of $\varphi$, a contradiction. Thus $a$ is uniform. First Extensionality gives uniqueness. ◻

The scheme of Lemma [3.1](#lem:collection) yields a uniform empty object $z$ (using $x\ne x$) and uniform singletons and unordered pairs of uniform objects. For uniform $a,b$, the Kuratowski pair $\langle a,b\rangle=\{\{a\},\{a,b\}\}$ exists uniformly. Its coordinates are uniquely recoverable by membership tests. An object belongs to every member of the pair exactly when it is $a$. If an object other than $a$ belongs to some member of the pair, it is $b$. Otherwise $b=a$. If $g$ and each of its members are uniform, a uniform $p$ may be adjoined to it using the defining formula $x\in_1g\lor x=p$. The result again has uniform members.

<a id="thm:omega"></a>

**Theorem 3.2** (Infinity without an Infinity axiom). $B$ proves the existence of a unique pair of objects $z,w$ such that $\operatorname{Zero}(z)$, $\operatorname{Ind}(z,w)$, and

$$
\forall t\,(\operatorname{Ind}(z,t)\to w\subseteq_1t).
$$

Moreover, $\operatorname{U}(w)$, $\forall x(x\in_1w\to\operatorname{U}(x))$, and $x\in_1w\leftrightarrow\operatorname{N}_z(x)$.

*Proof.* Let $P(a)$ assert that $a$ and all its first members are uniform. By Lemma [3.1](#lem:collection), $z$ exists and $P(z)$ holds. Whenever $P(a)$ holds, apply the lemma to $x=a\lor x\in_1a$. It gives a uniform successor $b$ whose first members are uniform. Any other successor of $a$ equals $b$ by First Extensionality. Thus the induction step of (B5) holds for $P$, and $P(a)$ holds for every $a$ satisfying $\operatorname{N}_z(a)$.

Apply Lemma [3.1](#lem:collection) to the $L_1$-formula $\operatorname{N}_z(x)$ with uniform parameter $z$. This yields a uniform object $w$ with precisely these first members, each uniform. Every inductive object contains $z$, so $z\in_1w$. If $a\in_1w$, the preceding argument supplies its successor $b$. Every inductive object contains $a$ and has a successor of $a$ as a member. By functionality, that successor is $b$. Consequently $b\in_1w$. Therefore $w$ is inductive, and its defining equivalence makes it a subset of every inductive object. Uniqueness of $z$ and $w$ follows by extensionality. ◻

We henceforth write $\omega=w$, $0=z$, and $N(a)$ for $a\in_1\omega$. Induction on $N$ with arbitrary $L$-formulas and parameters follows immediately from (B5). The alternative axiom presentation with explicit existence of a least inductive object and induction on its members is deductively equivalent to $B$: Theorem [3.2](#thm:omega) proves its axioms from $B$; in the other direction, leastness gives the equivalence of $N$ and $\operatorname{N}_z$, hence (B5). This equivalence holds also after adding $\mathsf{TI}_1$ or $\mathsf{US}_1$.

<a id="sec:arith"></a>

## 4. Arithmetic internal to DEST

We now work in an arbitrary model of $B$. In particular, its natural-number domain need not be externally standard. The construction uses internal induction, not induction on the metatheoretic natural numbers.

<a id="lem:numbers"></a>

**Lemma 4.1** (Number properties). *Every number is transitive, is not a first member of itself, and has only numbers as first members. Each number is zero or the successor of a number. The successor operation is total and injective on the numbers, and zero is not in its range. The first-membership relation is a strict linear order on the numbers.*

*Proof.* Totality and functionality follow from Theorem [3.2](#thm:omega) and extensionality. Transitivity follows by induction: if $x\in_1y\in_1S(a)$, then $y=a$ or $y\in_1a$, and transitivity of $a$ gives $x\in_1a$ in either case. Irreflexivity holds at zero. If $b=S(a)$ and $b\in_1b$, then $b=a$ or $b\in_1a$. The first case contradicts the irreflexivity of $a$, since $a\in_1b$; in the second, $a\in_1b\in_1a$ contradicts transitivity and irreflexivity of $a$. Induction likewise gives that all members of a number are numbers, that each nonzero number is a successor, and that zero belongs to every nonzero number. A successor contains its predecessor, so is nonempty. If distinct numbers $a,c$ have the same successor, then $a\in_1c$ and $c\in_1a$, contrary to transitivity and irreflexivity.

For comparison, fix a number $a$. Induction on $b$ gives

$$
a\in_1b\ \Longrightarrow\ S(a)=b\text{ or }S(a)\in_1b.
$$

Indeed, the base case is vacuous. If $b=S(c)$, then $a=c$ or $a\in_1c$; apply the induction hypothesis in the latter case. Now prove by induction on $a$ that every number $b$ equals $a$ or is comparable with it. The base case uses the fact that zero is a member of every nonzero number. At the successor step, if $b=a$ or $b\in_1a$, then $b\in_1S(a)$; if $a\in_1b$, use the displayed implication. Irreflexivity and transitivity exclude simultaneous opposite comparisons. Transitivity of the strict order follows from transitivity of the numbers as sets. ◻

<a id="lem:recursion"></a>

**Lemma 4.2** (Internal finite recursion). *Let $H(a,b,c)$ be an $L_1$-formula such that for every pair of numbers $a,b$ there is a unique number $c$ satisfying $H(a,b,c)$. For any numbers $a,i,n$, there is a unique value at $n$ of the recursion with initial value $i$ and step $H(a,\cdot,\cdot)$. The value relation is $L_1$-definable and satisfies the zero and successor equations.*

*Proof.* A recursion graph through $n$ is an object $g$ whose first members are exactly ordered pairs giving a function with domain the first members of $S(n)$, numerical values, initial value $i$ at zero, and the step condition whenever $k,l$ lie in its domain and $\operatorname{Succ}(k,l)$. The pair predicate is expressible by the first-language formulas for singletons and unordered pairs. Functionality, totality, and the transition condition are first-language formulas. The graph definition does not require a uniform graph.

We prove by internal induction on $n$ that such a graph exists and that it and its members are uniform. At zero, use the singleton of $\langle 0,i\rangle$. At the successor of $n$, let $c$ be the unique number satisfying $H(a,g(n),c)$, and adjoin $\langle S(n),c\rangle$. The new index $S(n)$ is not in the old domain, by irreflexivity, and the new domain is the old domain with that index adjoined. The only new transition has predecessor $n$, by successor injectivity. A transition from the new index to an old index would imply, by transitivity, that $S(n)$ belongs to the old domain. A transition from it to itself would contradict the irreflexivity of its successor. Lemma [3.1](#lem:collection) supplies the enlarged graph with the required uniformity properties. The induction formula asserts existence of a graph, so the argument covers nonstandard indices as well.

If two graphs through $n$ are given, induction on $k$ proves that their values agree whenever $k$ is in the common domain. The zero case is the initial condition; in the successor case, membership of $S(k)$ in the domain implies membership of $k$ there, by transitivity. Apply functionality of $H$. In particular the values at $n$ agree, even for nonuniform candidate graphs. Existence of an extended graph proves the recursion equation. The defining formula existentially quantifies over candidate graphs, with no reference to $\in_2$. ◻

Apply Lemma [4.2](#lem:recursion) first with initial value $a$ and step $c=S(b)$; denote its output by $a+n$. Then apply it with initial value zero and step $c=b+a$, and denote the output by $a\cdot n$. Thus

$$
\begin{aligned}
a+0&=a,& a+S(n)&=S(a+n),\\
a\cdot 0&=0,& a\cdot S(n)&=a\cdot n+a.
\end{aligned}
$$

All definitions are in $L_1$. The objects $0$ and $\omega$ are uniquely definable without parameters and may be eliminated by their defining formulas. The usual functional language of arithmetic is therefore interpreted definitionally via the graphs of these operations.

<a id="thm:pf"></a>

**Theorem 4.3** (Parameter-free second-order arithmetic). *Every model of $B$ yields a two-sorted model of $\mathsf{Z}_2^{\mathrm{pf}}$. Its first sort is the first-member domain of $\omega$, with the arithmetic just defined.*

*Proof.* Use the following domain for the second sort:

$$
\mathcal R=\{X:\forall x\,(x\in_1X\to N(x))\}.
$$

This is a domain predicate, not an assertion that the collection $\mathcal R$ is a set of DEST. Crucially, its definition does not require $\operatorname{U}(X)$. Membership of a number in a second-sort object is $\in_1$; equality is object equality, and First Extensionality gives set extensionality. The basic number axioms hold by Lemmas [4.1](#lem:numbers) and [4.2](#lem:recursion).

Relativize number quantifiers to $N$ and set quantifiers to the displayed domain predicate. For atomic arithmetic formulas, replace compound terms by their unique-value relations, and translate number-set membership by $\in_1$. Boolean connectives are unchanged. Induction on terms and formulas gives truth preservation; every translated formula belongs to $L_1$, even when set quantifiers alternate with number quantifiers. Full induction in the two-sorted structure follows from (B5), since its parameters need not be uniform.

For comprehension, let $\theta(n,\vec k)$ be any two-sorted formula without free set variables; its numerical parameters $\vec k$ are uniform. Bound set quantifiers are unrestricted. Its first-language translation $\theta^*(x,\vec k)$ yields the formula $N(x)\land\theta^*(x,\vec k)$, with only uniform parameters (including $\omega$ if used explicitly). All prospective members are uniform by Theorem [3.2](#thm:omega). Lemma [3.1](#lem:collection) gives a first-extension representative $A$, which belongs to $\mathcal R$ and realizes the comprehension instance. This proves the assertion. ◻

<a id="cor:lower"></a>

**Corollary 4.4** (Arithmetic lower bound). *If $\mathsf{Z}_2\vdash\sigma$ for a first-order arithmetic sentence $\sigma$, then $B\vdash\sigma^*$.*

*Proof.* Friedman’s restriction theorem ([5, Lemma 3.1.7](#ref-friedman)) gives, for a countable model of parameter-free full second-order arithmetic, a restriction of its set sort that satisfies full second-order arithmetic and retains the entire number structure. The comprehension scheme of $\mathsf{Z}_2^{\mathrm{pf}}$ supplies the instances used by that theorem. If $B\nvdash\sigma^*$, first-order completeness and downward Löwenheim–Skolem give a countable model of $B+\neg\sigma^*$. Theorem [4.3](#thm:pf) gives a countable parameter-free arithmetic model falsifying $\sigma$. After applying Friedman’s theorem, the resulting full model still falsifies $\sigma$, a contradiction. ◻

<a id="sec:upper"></a>

## 5. The powerset-free upper bound

We construct a set-coded model of each specified finite fragment of $T$ inside a powerset-free metatheory interpreted in $\mathsf{Z}_2$. We also arrange for the fragment model to agree with that metatheory on any specified sentence of the first membership language.

<a id="the-interpreted-metatheory-and-its-resources"></a>

### 5.1 The interpreted metatheory and its resources

By Kanovei and Lyubetsky ([7, Theorems 5.2 and 1.2](#ref-kl)), $\mathsf{Z}_2$ (their $\mathsf{PA}_2^-$) interprets a tree-based model of the intermediate set theory $\mathsf{TMC}$. Inside that model, the constructible cut $L^*$ satisfies powerset-free ZFC with Collection. It is $L_{\omega_1^L}$ when the first uncountable ordinal of $L$ exists, and $L$ otherwise. The following lemma identifies the numbers and arithmetic operations through both interpretations.

<a id="lem:arithmetic-preservation"></a>

**Lemma 5.1** (Preservation of arithmetic). Let $\mathcal A$ be any Henkin model of $\mathsf{Z}_2$ with number domain $N$ and set domain $\mathcal R$. Let $\mathcal V$ be its tree interpretation of $\mathsf{TMC}$ as in ([7, Definition 5.1 and Theorem 5.2](#ref-kl)), and let $\mathcal S$ be the constructible cut $L^*$ of $\mathcal V$. The number structure of $\mathcal A$ is isomorphic to the von Neumann number structure of $\mathcal S$, with its usual recursively defined arithmetic. In particular, for every first-order arithmetic sentence $\sigma$,

$$
\mathcal A\models\sigma
\quad\Longleftrightarrow\quad
\mathcal S\models\sigma^*.
$$

*Proof.* All sequence coding in this proof is internal to $\mathcal A$. For $n\in N$, let $T_n$ be the tree of internally finite strictly decreasing sequences of numbers less than $n$. Let $T_\omega$ be the tree of all internally finite strictly decreasing sequences of numbers. Both definitions include the empty sequence. These are coded sets of numbers in $\mathcal R$ by arithmetical comprehension. None of these trees has an internally coded infinite branch: along a branch starting with $k$, induction would force its successive entries to decrease at least by one at each step, which is impossible after $k+1$ further steps. Thus each is a well-founded tree in the sense of the interpretation, even if $N$ is externally nonstandard.

Write $[T]$ for the element of $\mathcal V$ represented by a tree $T$, modulo the bisimulation equivalence of ([7, Definition 5.1](#ref-kl)). The subtree of $T_n$ below its one-term node $\langle k\rangle$, with its first entry removed from each sequence, is exactly $T_k$ for $k<n$. The corresponding subtree of $T_\omega$ is $T_k$ for each $k\in N$. By the definition of interpreted membership, the following descriptions are exhaustive (with the displayed families understood externally):

$$
\begin{aligned}
&=\{[T_k]: k<n\},\\
[T_\omega]&=\{[T_k]: k\in N\}.
\end{aligned}
$$

Here and below, a description by members is justified by Extensionality in $\mathcal V$; it does not require a new set-existence principle. Consequently $[T_0]$ is the empty set and, for all $n\in N$,

$$
[T_{S(n)}]=[T_n]\cup\{[T_n]\}.
$$

If $k<n$, then $[T_k]\in[T_n]$; Foundation in $\mathcal V$ excludes equality in this case. Linearity of the arithmetic order therefore makes the assignment $j(n)=[T_n]$ injective.

The object $[T_\omega]$ is inductive in $\mathcal V$. To see leastness, take any inductive object $a$ of $\mathcal V$, represented by a tree code $A$. The assertion $[T_n]\in a$ translates to a two-sorted formula with parameter $A$: the definition of $T_n$ is uniform in $n$, and interpreted membership is definable by the bisimulation relation. The assertion holds at zero and passes from $n$ to $S(n)$ by inductiveness. Full induction in $\mathcal A$ therefore gives $[T_n]\in a$ for every $n\in N$. This proves that $[T_\omega]$ is precisely the least inductive set $\omega^{\mathcal V}$ and that $j$ is a bijection from $N$ onto its members.

It remains to check the constructible restriction. In the hierarchy used by Kanovei and Lyubetsky, the initial level for the empty real is $L_0[\varnothing]=\omega^{\mathcal V}\cup\{\varnothing\}=\omega^{\mathcal V}$; see equation (3) and Lemma 6.2 of ([7](#ref-kl)). The next level contains $\omega^{\mathcal V}$ itself, as the subset of the initial level defined by $x=x$. Both levels lie in $L^*$, since in the bounded case $\omega_1^L$ is greater than $1$. Thus $\omega^{\mathcal V}$ and all its members are retained. Empty set and successor agree in the cut and in $\mathcal V$ by transitivity. Every inductive object of the cut is also inductive in $\mathcal V$, since its members and their successor witnesses are retained. Hence $\omega^{\mathcal S}=\omega^{\mathcal V}$.

Finally, the cut has the usual number operations, defined by the finite recursion graphs described in Lemma [4.2](#lem:recursion). Their existence in the cut follows from ordinary finite recursion in powerset-free set theory with Collection (Section [5.2](#sec:histories)), rather than from any DEST axiom. Denote these operations by $+_{\mathcal S}$ and $\cdot_{\mathcal S}$. Their zero and successor equations hold in $\mathcal S$. For fixed $a\in N$, the assertions comparing $j(a+n)$ with $j(a)+_{\mathcal S}j(n)$, and $j(a\cdot n)$ with $j(a)\cdot_{\mathcal S}j(n)$, are definable in $\mathcal A$: the numeral codes, the tree interpretation and the constructible cut are definable there. Induction on $n$ in $\mathcal A$, first for addition and then for multiplication, yields

$$
\begin{aligned}
j(a+n)&=j(a)+_{\mathcal S}j(n),\\
j(a\cdot n)&=j(a)\cdot_{\mathcal S}j(n).
\end{aligned}
$$

The base cases use zero preservation, and the successor steps use successor preservation and the respective recursion equations (and addition preservation for multiplication). Thus $j$ preserves all the arithmetic primitives. If order is included, it is preserved by the membership description of the numerals. Induction on the syntax of a first-order arithmetic formula now gives the stated truth equivalence, since its number quantifiers range over domains in bijective correspondence. No induction over externally standard numerals, nor any external countable-choice principle for selecting their codes, is used. ◻

Write $\mathcal S$ for the constructible cut in Lemma [5.1](#lem:arithmetic-preservation). The internal proof requires the following resources.

**(R1)** Extensionality, Empty Set, Adjunction, Union, a least inductive set $\omega$, Foundation, and full Separation and Collection. Here adjunction sends $(x,y)$ to $y\cup\{x\}$.

**(R2)** A definable strict class order under which every nonempty definable class has a least element.

**(R3)** Cofinal finite reflection. For any set $a$ and any externally fixed finite family of first-order formulas $\chi_i(x,\vec p)$, there is a transitive set $d$ with $a\in d$, closed under adjunction, such that

$$
\vec p\in d^{|\vec p|}\ \land\ \bigl(\mathcal S\models\exists x\,\chi_i(x,\vec p)\bigr)
  \ \Longrightarrow\
  \exists x\in d\;\mathcal S\models\chi_i(x,\vec p)
$$

for each $i$.

**(R4)** Internal countability. Every nonempty set in $\mathcal S$ is the range of a function from $\omega$ whose graph belongs to $\mathcal S$.

For (R1), use the axioms of the cut ([7, Theorem 8.6](#ref-kl)). Separation and leastness of $\omega$ give induction for definable predicates on $\omega$. For (R2), use the order of ([7, Lemma 7.3](#ref-kl)), in its class or limit-level form as appropriate. The initial segment up to a given witness is contained in a constructible level, so Separation and the well-order on that level give the least witness.

For (R3), expand any defined operations and relations into the membership language. Apply cofinal reflection ([7, Corollary 8.4 and Lemma 8.5](#ref-kl)) to the conjunction of the formulas $\exists x\,\chi_i(x,\vec p)$, with the parameter variables left free, and include the adjunction request $z=y\cup\{x\}$. Reflection of these existential subformulas and their matrices gives the required witnesses in a limit level $d=L_\beta$ containing $a$ as a member. The level is transitive. It is a set of the cut because $L_\beta\in L_{\beta+1}$, and $\beta+1<\omega_1^L$ in the bounded case. Adjunction is total and uniquely defined in the cut, so reflection of its graph gives closure of $d$ under that operation.

For (R4), use internal countability of both forms of the constructible cut ([8, Section 1 and Lemmas 15 and 17(1)](#ref-kl2)). This result is proved there in the Simpson set-theoretic setting, which is available in the stronger $\mathsf{TMC}$ setting as explained in that paper. For a nonempty set, an injection into $\omega$ gives an internal enumeration by taking its inverse on its range and using a fixed member elsewhere. The graph exists by Separation and Collection. These resources give the fields and hypotheses used in the Lean weak-model construction. In particular, the order and adjunction symbols of its language are interpreted by definable relations and operations.

Every reference to a formula in the construction below denotes an externally fixed formula, with parameters varying over sets of $\mathcal S$. The interpretation and reflection facts can be applied separately to each such finite list. No truth predicate for the ambient universe is assumed. All set notation and internal induction in this section are interpreted in $\mathcal S$, including in nonstandard models. In particular, an internally finite history need not be finite externally.

<a id="sec:histories"></a>

### 5.2 Internal finite histories without Power Set

We record the set-existence argument used by the matching procedure. In powerset-free set theory with Collection, a definable functional relation on a set has a graph and a range: Collection gathers a set of witnesses, Separation removes extraneous witnesses, and the same argument applied to ordered-pair codes yields the graph. Finite products are obtained by collecting rows and taking unions. For an everywhere-defined functional update $h$ on states, define a history through $n$ to be a graph with domain $n+1$, a prescribed initial state, and consecutive values related by $h$. Start with a singleton history and extend it by one step by adjoining the next ordered pair. Internal induction gives existence at each internal $n$ and uniqueness by induction comparing two histories on their common domain. Collection gathers histories for all $n\in\omega$; Separation discards any extraneous objects that are not histories. The union of their compatible graphs gives a sequence. Equivalently, define the graph by the condition that an entry occurs in a history, then collect the ordered pairs and apply Separation. For a definable update specified by a finite case distinction, its graph is first-order definable. This is sufficient for all recursions below and requires no set of possible histories.

<a id="sec:regions"></a>

### 5.3 Reflecting domains and requested extensions

Fix a finite list $Q$ of unary defining formulas $\varphi(x,\vec p)$ of $L_1$; their parameters may have any fixed finite arity. The intended fragment includes both extensionality axioms, the comprehension and uniformity instances from $Q$, and all the natural-number and set-induction instances. Fix also a first-language sentence $s$ whose truth is to be retained. When reading $L_1$ in $\mathcal S$, the first relation is its ordinary membership.

For each formula in $Q$ and for $s$, include requests for witnesses to existential subformulas (or counterexamples to universal subformulas). For every $\varphi$ in $Q$, include the following requests, with the indicated parameters:

$$
\begin{aligned}
&\varphi(x,\vec p) &&\text{positive witness},\\
&\forall y\,(y\in x\leftrightarrow\varphi(y,\vec p)) &&\text{representative},\\
&\neg(x\in a\leftrightarrow\varphi(x,\vec p)) &&\text{disagreement},\\
&\varphi(x,\vec p)\land x\notin u\land x\notin b &&\text{outside witness}.
\end{aligned}
$$

Include also the outside request for the always-true formula. The variables $a,u,b$ here are additional request parameters. The request for a representative concerns the entire $\mathcal S$-universe, not just the reflecting domain.

Apply (R3) first with $a=\omega$, obtaining a transitive region $u$ containing $\omega$, then with $a=u$, obtaining a transitive adjunction-closed region $d$ containing $u$. Both regions are closed under the same finite list of requests. In particular, $u\subseteq d$, and $d$ contains all numbers of $\mathcal S$ and its $\omega$. We use $d$ as the carrier, with inherited membership as its first relation. Its first extensions are the actual ambient sets $a$ for $a\in d$, by transitivity. Extensionality of this restricted relation follows from ambient Extensionality.

By induction on the syntax of the fixed formulas, closure under subformula requests gives

<a id="eq:reflect"></a>
$$
d\models\varphi(x,\vec p)
\quad\Longleftrightarrow\quad
\mathcal S\models\varphi(x,\vec p),
\qquad x,p_1,\ldots,p_k\in d.\tag{5.1}
$$

The analogous equivalences hold for $s$ and for the formulas of $Q$ evaluated in $u$ with parameters in $u$. The atomic cases use the restriction of membership and equality; connectives preserve the equivalence. For quantifiers, an ambient existential witness or universal counterexample can be found in the reflecting region. This is finite-formula reflection, not an assertion of full elementarity.

For a tuple $\vec p$ of elements of $d$, write

$$
E_{\varphi,\vec p}=\{x\in d:d\models\varphi(x,\vec p)\}.
$$

This set exists by Separation on $d$. Call a set $E$ *protected* if it is such an extension for some $\varphi\in Q$ and parameters in $u$. We prescribe $F(a)=a$ for all $a\in u$. The remaining left and right domains are

$$
\begin{aligned}
 O&=d\setminus u,\\
 J&=\left(\{\{a\}:a\in O\}\cup
      \{E_{\varphi,\vec p}:\varphi\in Q,\ \vec p\in d^{k_\varphi}\}\right)\setminus u,
\end{aligned}
$$

where $k_\varphi$ is the parameter arity. All elements of $J$ are subsets of $d$. The right-hand family exists by finite products, Separation and Collection; alternatively, as in the Lean construction, take a larger reflecting region containing $d$ and closed under the requests for the extensions of all parameter tuples, and separate $J$ from that region. The singleton sets are obtained by adjunction in the larger region. This family contains only the requested extensions and the indicated singletons, rather than the entire ambient powerset of $d$.

<a id="lem:fresh"></a>

**Lemma 5.2** (Availability of fresh matches). *In the notation above the following statements hold.*

**(a)** *If $E\in J$ is protected, its defining class has no ambient representative, and $E\notin d$.*

**(b)** *Given any $b\in d$ and any protected $E\in J$, there exists $x\in E\cap O$ with $x\notin b$.*

**(c)** *For every $b\in d$ there exists $x\in O$ with $x\notin b$.*

**(d)** *For every $x\in O$, $\{x\}\in J$ and $\{x\}$ is not protected.*

*Proof.* (a) Take a protected definition $\varphi(x,\vec p)$ with parameters in $u$. If the ambient class has a representative $a$, the representative request in $u$ supplies one in $u$. By transitivity and [(5.1)](#eq:reflect), its extension equals $E$, contrary to $E\notin u$. If $E\in d$, an ambient disagreement between $E$ and the defining class would be witnessed in $d$, by the disagreement request with parameters $E,\vec p$. This contradicts the definition of $E$ and [(5.1)](#eq:reflect). Hence $E$ itself would be an ambient representative, which has just been ruled out.

\(b\) If no ambient $\varphi$-witness lay outside $u\cup b$, Separation on that union would represent the whole defining class. Thus a witness exists outside both sets. Since $u,b,\vec p\in d$, the outside request in $d$ supplies such a witness in $d$. By [(5.1)](#eq:reflect) it belongs to $E$, and by construction it is outside $u$ and $b$.

\(c\) Apply the same argument to the formula that is always true: a set containing all sets would contain itself, contrary to Foundation. Thus there is an ambient witness outside $u\cup b$, and the true-formula outside request puts one in $d$.

\(d\) Transitivity of $u$ implies $\{x\}\notin u$, so it belongs to $J$. If it were protected, [(5.1)](#eq:reflect) would give an ambient positive witness for its defining formula. The positive request in $u$ would supply a witness in $u$. That witness belongs to the singleton by [(5.1)](#eq:reflect), and must equal $x$, a contradiction. ◻

<a id="sec:matching"></a>

### 5.4 An internal back-and-forth

For $a\in O$ and $E\in J$, call $(a,E)$ admissible when

<a id="eq:allowed"></a>
$$
a\ne E\quad\land\quad(E\text{ is protected}\;\to\;a\in E).\tag{5.2}
$$

By Lemma [5.2](#lem:fresh)(c,d), both $O$ and $J$ are nonempty. They admit internal enumerations by (R4). We construct a bijection $f:O\to J$ whose graph consists of admissible matches. Each internally finite partial matching state includes a forbidden set $b\in d$ of used left points and singleton indices of any used singleton outputs from $O$. Start with the empty matching and the empty forbidden set. At each step, any additional forbidden points are in $d$, so adjunction closure keeps the forbidden set in $d$. For a used singleton output $\{x\}$, its index $x\in O$ is unique. Whether an output has this form is a definable test, and the set is updated accordingly.

For the next left point $a$, do nothing if it is matched. Otherwise choose an unused singleton output $\{x\}$ with $x\in O$ outside the forbidden set. Also exclude the unique possible $x$ such that $a=\{x\}$, by adjoining that index to the forbidden set if it lies in $d$. Lemma [5.2](#lem:fresh)(c,d) ensures the required singleton exists, is unprotected and belongs to $J$. The new pair is admissible.

For the next right point $E$, do nothing if it is already matched. Otherwise, if $E$ is protected, choose $a\in E\cap O$ outside the forbidden set by Lemma [5.2](#lem:fresh)(b); $a\ne E$ by (a). If $E$ is not protected, choose $a\in O$ outside the forbidden set, also excluding $E$ if $E\in d$. Lemma [5.2](#lem:fresh)(c) gives such an $a$. In either case the new pair is admissible. The update preserves injectivity and enlarges the matching, and updates the forbidden set to include the newly used points or singleton indices, as appropriate.

Choose witnesses by the definable least-witness operation, or the least eligible index of the relevant enumeration. Perform a left step and a right step at each natural-number stage. The update is definable because $Q$ is a fixed finite list and the tests of membership, equality, protection and availability are first-order formulas. Section [5.2](#sec:histories) supplies internal histories, and induction verifies their finite matching invariants and monotonicity. The union of the compatible graphs is an internal function: any two recorded pairs occur together at a common later stage and hence obey functionality and injectivity. Each point in either enumeration is handled at its corresponding stage. Thus the union is the desired bijection, with a graph that is a set in $\mathcal S$. This argument uses internal induction, including at nonstandard indices; it does not rely on an external enumeration of the domain.

Extend $f$ by the prescribed assignments $F(a)=a$ on $u$. The resulting $F$ is injective because its two pieces have disjoint domains and disjoint ranges. It is a bijection from $d$ onto $u\cup J$, all of whose elements are subsets of $d$. Define

<a id="eq:relations"></a>
$$
\begin{aligned}
x\in_1a&\iff x\in a,\\
x\in_2a&\iff x\in F(a),
\end{aligned}
\qquad x,a\in d.\tag{5.3}
$$

In particular, the graph of $\in_2$ is a set by Separation on $d\times d$; the implementation uses separation in a larger region containing the required pairs. Since both $a$ and $F(a)$ are subsets of $d$, Extensionality implies

<a id="eq:fixed"></a>
$$
\operatorname{U}(a)\quad\Longleftrightarrow\quad a=F(a)\quad\Longleftrightarrow\quad a\in u.\tag{5.4}
$$

The last equivalence follows from the fixed-point exclusion of [(5.2)](#eq:allowed). The construction is not an assignment of arbitrary subsets to objects, but a constrained bijection between internally collected families.

<a id="sec:verifyfrag"></a>

### 5.5 Axioms and preservation of arithmetic

<a id="thm:fragment"></a>

**Theorem 5.3** (Internal fragment model). *For every fixed finite family $Q$ of first-language defining formulas and every first-language sentence $s$, the resources (R1)–(R4) suffice to construct a set-coded structure $\mathcal D=(d,\in_1,\in_2)$ satisfying both extensionality axioms, comprehension and uniformity for $Q$, and every externally fixed instance of relational natural-number induction and first-membership set induction. Moreover, $\mathcal D\models s$ if and only if $\mathcal S\models s$.*

*Proof.* First Extensionality follows from transitivity of $d$; Second Extensionality from injectivity of $F$. Every requested extension is in $u$ or $J$, hence has a representative under $F$. This proves comprehension. Suppose the parameters of a requested instance of uniformity are uniform, and its extension is $E=F(a)$. By [(5.4)](#eq:fixed), the parameters lie in $u$, so $E$ is protected. If $a\notin u$, admissibility implies $a\in E$, i.e. $a\in_2a$. Therefore the non-self-membership premise forces $a\in u$, which is precisely uniformity.

The empty object, the internal numbers of $\mathcal S$, and $\omega$ all belong to $d$. Transitivity makes the empty object and successor relation agree with those of $\mathcal S$ whenever the objects in question belong to $d$. Consequently $\omega$ is inductive in $\mathcal D$. If $t$ is inductive in $\mathcal D$, induction in $\mathcal S$ shows $n\in t$ for all $n\in\omega$. The base holds by inductiveness of $t$, and the successor witness in $d$ must be the successor computed in $\mathcal S$. Thus $\omega$ is least inductive in $\mathcal D$, and $\operatorname{N}_z$ there picks out exactly the numbers of $\mathcal S$.

For any fixed induction formula, relativize its quantifiers to $d$ and translate second membership by [(5.3)](#eq:relations), using the graph of $F$ as a parameter in $\mathcal S$. Induction in $\mathcal S$ applied to this translation proves (B5). For $\mathsf{TI}_1$, separate in $\mathcal S$ the set of points of $d$ falsifying the translated predicate. If it is nonempty, Foundation in $\mathcal S$ gives a minimal counterexample, contradicting progressiveness. Both arguments apply to formulas with arbitrary parameters and both membership symbols. Finally, [(5.1)](#eq:reflect) gives preservation of $s$ because it is a first-language sentence. ◻

<a id="rem:matching"></a>

**Remark 5.4** (Set existence in the matching argument). Only extensions of fixed formulas over specified sets are collected. The fresh-witness argument uses nonrepresentability and Separation, not a cardinality estimate for an ambient proper class. The matching uses set-coded enumerations and internally finite histories, not external choice or a set of all partial maps. The graph of second membership and the induction counterexamples are sets of the weak model. These facts are necessary to apply internal Foundation and induction. Merely showing that a matching exists externally would not suffice.

<a id="sec:exact"></a>

## 6. Exact arithmetic strength

<a id="thm:upper"></a>

**Theorem 6.1** (Upper bound and arithmetic preservation). *For any first-order arithmetic sentence $\sigma$, if $T\vdash\sigma^*$ then $\mathsf{Z}_2\vdash\sigma$. Also, any Henkin model of $\mathsf{Z}_2$ yields, externally, a model of $T$.*

*Proof.* Fix a finite derivation of $\sigma^*$ in $T$. There are finitely many comprehension and uniformity formulas in it; let $Q$ contain them. Choose $s=\sigma^*$ in Theorem [5.3](#thm:fragment). Given any model of $\mathsf{Z}_2$, apply the published tree interpretation and pass to the constructible cut to obtain a weak set model with (R1)–(R4). The theorem gives an internal model of the finite axiom support of the derivation, retaining the truth of $s$. Ordinary soundness applied to that finite derivation yields $\mathcal D\models\sigma^*$, so $\mathcal S\models\sigma^*$. Lemma [5.1](#lem:arithmetic-preservation) identifies the von Neumann interpretation of arithmetic in $\mathcal S$ with the original number structure, including its addition and multiplication. Hence the original arithmetic model satisfies $\sigma$. Since the model of $\mathsf{Z}_2$ was arbitrary, first-order completeness gives $\mathsf{Z}_2\vdash\sigma$.

For the second assertion, start with any model of $\mathsf{Z}_2$ and its interpreted weak set model. Every externally specified finite subset of $T$ has a model by Theorem [5.3](#thm:fragment), taking $s$ to be a logical truth. Classical first-order compactness (see ([10](#ref-enderton))), used externally, supplies one model of $T$. This step does not assert that the interpreted weak theory proves a single internal truth predicate for all fragments, nor that $\mathsf{Z}_2$ proves $\operatorname{Con}(T)$. ◻

<a id="cor:exact"></a>

**Corollary 6.2** (Equiconsistency and equal arithmetic consequences). For every first-order arithmetic sentence $\sigma$,

$$
\mathsf{Z}_2\vdash\sigma\quad\Longleftrightarrow\quad B\vdash\sigma^*
\quad\Longleftrightarrow\quad T\vdash\sigma^* .
$$

In particular, $\operatorname{Con}(\mathsf{Z}_2)\leftrightarrow\operatorname{Con}(B)\leftrightarrow\operatorname{Con}(T)$.

*Proof.* Combine Corollary [4.4](#cor:lower), the inclusion $B\subseteq T$, and Theorem [6.1](#thm:upper). For the consistency equivalences one may either use an arithmetic contradiction in the comparison, or combine the model transformations, Friedman’s restriction and first-order completeness. No form of uniform subsethood is used in this argument. ◻

The consistency equivalences are in the external metatheory. The arithmetic comparison uses the interpretations on the entire number domain on each side, as established in Corollary [4.4](#cor:lower) and Lemma [5.1](#lem:arithmetic-preservation).

<a id="sec:rank"></a>

## 7. Uniform subsethood and a ZF relative-consistency bound

The additional principle $\mathsf{US}_1$ requires every object whose first extension is contained in a uniform object’s first extension to be uniform. The preceding powerset-free construction does not automatically enforce this condition: its uniform region must be changed to one with an appropriate subset-closure property. We give a separate finite-fragment argument over ZFC, then pass to ZF through constructibility.

<a id="thm:rank"></a>

**Theorem 7.1**. *If ZF is consistent, then $B+\mathsf{US}_1+\mathsf{TI}_1$ is consistent.*

*Proof.* Work first in ZFC, and fix an externally specified finite fragment of the displayed theory. Let $Q$ contain the finitely many first-language formulas in its uniformity instances. For each $\varphi(x,\vec p)\in Q$, include in a finite reflection family $\varphi$, the positive-witness formula $\exists x\,\varphi(x,\vec p)$, the representative formula

$$
R_\varphi(a,\vec p)\mathrel{:\Longleftrightarrow}\forall x\,(x\in a\leftrightarrow\varphi(x,\vec p)),
$$

and $\exists a\,R_\varphi(a,\vec p)$, together with the required subformulas. By finite Lévy–Montague reflection (see ([11](#ref-jech))), choose limit ordinals $\omega<\alpha<\beta$ such that $V_\alpha$ and $V_\beta$ agree on these formulas for parameters in $V_\alpha$. Both levels are transitive. Choose a countable elementary substructure $M$ of $(V_\beta,\in,V_\alpha)$, where the last entry is a unary predicate, containing $\omega$ and every finite ordinal. Put $U=M\cap V_\alpha$.

For $a\in M$ let $E(a)=\{x\in M:x\in a\}$. By elementarity and ambient Extensionality, the map $a\mapsto E(a)$ is injective. Let $D$ be the family of all subsets of $M$ definable in the first language with parameters from $M$. It is countable, since the language and $M$ are countable. It contains $E(a)$ for all $a\in M$ and all singletons of members of $M$. Prescribe $F(a)=E(a)$ for $a\in U$. Call $C\in D$ protected if some formula in $Q$ defines $C$ over $M$ with parameters from $U$.

We verify the matching conditions, now in terms of traces. Suppose $C$ is protected, defined by $\varphi(x,\vec p)$ with $\vec p\in U$. Write $C^*=\{x\in V_\beta:V_\beta\models\varphi(x,\vec p)\}$. If $C^*$ has a representative in $V_\beta$, reflection supplies a representative in $V_\alpha$ and elementarity in the expanded language supplies one in $U$. Its trace is $C$. Conversely, if $C=E(a)$ for $a\in M$, elementarity makes $a$ a representative of $C^*$ in $V_\beta$; the preceding argument and trace injectivity imply $a\in U$. Thus, a protected extension not already fixed has no representative in $V_\beta$.

In this last case $C^*$ is unbounded in rank below $\beta$: any subset of $V_\beta$ of bounded rank is an element of $V_\beta$, since $\beta$ is limit. Hence $C^*$ has arbitrarily many points outside $V_\alpha$. By elementarity with the extra predicate, $C$ contains arbitrarily many points of $M\setminus U$, avoiding any prescribed finite list of elements of $M$. There are also arbitrarily many points of $M\setminus U$ without any condition on membership in $C$, by the same elementarity argument applied to the ranks between $\alpha$ and $\beta$.

For $b\in M\setminus U$, the singleton $\{b\}$ is not a fixed trace: a representative from $U$ would, by elementarity, have $b$ as an actual member, contradicting transitivity of $V_\alpha$. Nor is it protected. If it were defined by a formula from $Q$ with parameters in $U$, positive-witness reflection to $V_\alpha$, followed by elementarity in the expanded language, would produce a member of $U$ in that singleton.

Complete the prescribed assignments by the countable back-and-forth used in Section [5.4](#sec:matching), with left domain $M\setminus U$, right domain $D\setminus\{E(a):a\in U\}$, and admissibility condition

$$
E(a)\ne C\quad\land\quad(C\text{ is protected}\;\to\;a\in C).
$$

For an unmatched left point, use a fresh unprotected singleton, avoiding its first trace. For an unmatched right point, use a fresh member outside $U$ of the extension if it is protected (its trace cannot equal that extension), and otherwise any fresh outside point avoiding the at most one point with that trace. The properties just proved ensure all choices. This produces a bijection $F:M\to D$ such that $F(a)=E(a)$ exactly on $U$.

Let $x\in_1a$ mean $x\in a$ in the inherited structure and $x\in_2a$ mean $x\in F(a)$. Both Extensionalities hold, and surjectivity realizes comprehension. Uniform objects are precisely $U$, and the protected-extension condition gives all requested uniformity instances, as in Theorem [5.3](#thm:fragment).

To verify $\mathsf{US}_1$, suppose $a\in U$ and the first trace of $b$ is included in that of $a$. Elementarity implies $V_\beta\models b\subseteq a$, hence $b\subseteq a$ in the ambient universe by transitivity. Since $a\in V_\alpha$, rank monotonicity for subsethood gives $b\in V_\alpha$, so $b\in U$. This is precisely $\mathsf{US}_1$.

The first relation is well-founded in the ambient metatheory, so every instance of $\mathsf{TI}_1$ holds, even for formulas involving the second relation. Since $\omega$ and every finite ordinal of the ambient ZFC universe are in $M$, the first members of $\omega$ in $M$ are those finite ordinals. Successor is preserved because its defining formula holds in $V_\beta$ and elementarity transfers it to $M$. Induction in the ambient universe shows that each inductive object in $M$ contains all these numbers. It also verifies (B5) on the resulting least inductive set.

Thus, each specified finite fragment has a model in ZFC. For ZF, perform this fixed-fragment argument in the constructible universe $L$, which satisfies ZFC. The resulting set structure satisfies the specified fragment also in the surrounding universe, by absoluteness of satisfaction for fixed first-order formulas in set structures. Equivalently, any model of ZF admits the corresponding interpreted construction in its $L$. If ZF is consistent, first-order completeness and external compactness therefore give the asserted consistency. No single truth predicate for all fragments, inaccessible cardinal, or internal proof of $\operatorname{Con}(\mathsf{ZF})$ is used. ◻

The corresponding Lean theorem constructs a model of $B+\mathsf{US}_1+\mathsf{TI}_1$ in its ambient type theory. It uses a rank cut of `ZFSet` closed under all the specified witness queries and a countable hull. The finite-reflection argument above supplies the separate reduction to ZF.

<a id="sec:zermelo"></a>

## 8. A hereditarily uniform Zermelo domain

We now work in an arbitrary model of $B^+=B+\mathsf{US}_1$. Membership and subsethood in this section are taken with respect to $\in_1$. A set is transitive if every member of a member also belongs to it. A set $a$ is *internally well-founded on its members* if every nonempty object $b\subseteq_1a$ has a member with no first member in $b$. The definition quantifies over subsets represented by objects of the model.

<a id="def:hered"></a>

**Definition 8.1**. An object $a$ is hereditarily uniform if $\operatorname{U}(a)$ and there is a transitive $t$ with $a\subseteq_1t$ and $\forall x(x\in_1t\to\operatorname{U}(x))$.

This witness formulation is equivalent to the existence of a least transitive superset of $a$ with uniform members, together with $\operatorname{U}(a)$. Indeed, given a witness $t$, form the intersection of all transitive supersets of $a$, using the first-language formula for membership in that intersection with uniform parameter $a$. Its values are members of $t$ and hence uniform, so Lemma [3.1](#lem:collection) applies. The resulting intersection is transitive, contains $a$ as a subset, and is the least such superset. A transitive uniform object with uniform members is itself such a witness.

<a id="lem:powerset"></a>

**Lemma 8.2** (Uniform powersets). For every uniform $a$, there is a unique uniform $b=\mathcal P_1(a)$ with uniform members such that

$$
x\in_1b\quad\Longleftrightarrow\quad x\subseteq_1a.
$$

If $a$ is transitive and well-founded on its members, then so is $b$.

*Proof.* By $\mathsf{US}_1$, all prospective members of the first-language subset formula with parameter $a$ are uniform. Lemma [3.1](#lem:collection) gives the asserted $b$. For transitivity, if $y\in_1x\in_1b$, then $y\in_1a$, and since $a$ is transitive, $y\subseteq_1a$, so $y\in_1b$. Also, $a\subseteq_1b$ by transitivity of $a$.

For well-foundedness let $d\subseteq_1b$ be nonempty. It is uniform by $\mathsf{US}_1$. Every member of $a$ is a subset of $a$ by transitivity, hence is uniform by $\mathsf{US}_1$. If $d$ has a member in $a$, the nonempty intersection $e=d\cap a$ exists by Lemma [3.1](#lem:collection), since its parameters and prospective members are uniform. Choose a minimal member $x$ of $e$ using well-foundedness of $a$. Any first member of $x$ belonging to $d$ belongs to $a$ by transitivity, and so belongs to $e$, a contradiction. If $d$ has no member in $a$, every member $x$ of $d$ is minimal in $d$: all its first members lie in $a$, since $x\in_1b$. This proves the result. ◻

<a id="lem:omega-good"></a>

**Lemma 8.3**. *The object $\omega$ is uniform, transitive, has uniform members, and is well-founded on its members.*

*Proof.* Uniformity is Theorem [3.2](#thm:omega); transitivity is Lemma [4.1](#lem:numbers). Let $d\subseteq_1\omega$ be a nonempty object without a minimal member. Induct on numbers $n$ in the assertion that $n\notin_1 d$ and no member of $n$ belongs to $d$. The base follows from emptiness of zero and the assumption that $d$ has no minimal member. If the assertion holds at $n$, no member of $S(n)$ belongs to $d$. Were $S(n)$ itself in $d$, it would be minimal. Thus the assertion holds at the successor. It follows that $d$ has no member, a contradiction. This uses (B5), with parameter $d$, not ambient set induction. ◻

<a id="internal-powerset-stages"></a>

### 8.1 Internal powerset stages

For every internal number $n$, we define a stage $A_n$ by an internal recursion satisfying

<a id="eq:stages"></a>
$$
A_0=\omega,\qquad A_{S(n)}=\mathcal P_1(A_n).\tag{8.1}
$$

We must establish a single first-language stage relation, not just construct an external sequence for the standard numbers. Let $\operatorname{Stage}(n,a)$ assert that there exists a first-membership graph with natural-number indices through $n$, initial value $\omega$, and transitions given by the first-language power relation

$$
\operatorname{Power}(v,w)\mathrel{:\Longleftrightarrow}\forall y\,(y\in_1w\leftrightarrow y\subseteq_1v),
$$

whose value at $n$ is $a$. The graph is coded by the uniform ordered-pair convention where pairs exist; its definition itself makes no uniformity demand. Explicitly one can use graphs with domain the first extension of $S(n)$, require a unique value at each index, and assert the initial and transition equations. Equivalently one can allow downward-closed graphs, requiring each recorded nonzero index to have its predecessor recorded, as in the formalization. Internal induction on the index gives the same stage values in both descriptions.

Induct on $n$ in the assertion that such a graph exists, is uniform with uniform members, and records uniform stage values having uniform members. At zero, take the singleton pair $\langle 0,\omega\rangle$. If a graph exists through $n$, Lemma [8.2](#lem:powerset) supplies the uniform powerset of its last value. Adjoin its ordered pair at $S(n)$ by Lemma [3.1](#lem:collection), exactly as in Lemma [4.2](#lem:recursion). The index is new and no earlier transition changes. This proves existence for all internal indices. The uniqueness of stage values for any candidate graph follows by induction: the zero value is prescribed, and powers are unique by First Extensionality. No Replacement is used. Every graph-based condition here is a first-language formula, except for the uniformity assertions in the induction proof, which are permitted full-language formulas.

By Lemmas [8.2](#lem:powerset) and [8.3](#lem:omega-good), induction also shows that each stage is transitive and well-founded on its members, and is uniform with uniform members. Since a transitive object is contained in its own powerset, the stages are nested. More explicitly, induction on $n$ proves $A_k\subseteq_1A_n$ whenever $k\in_1n$ or $k=n$: at a successor use the corresponding property at its predecessor and $A_n\subseteq_1A_{S(n)}$. Comparability of number indices from Lemma [4.1](#lem:numbers) consequently places any two stage members into a common stage. The equality, existence and nesting statements concern all internal numbers, including nonstandard ones.

<a id="thm:zermelo"></a>

**Theorem 8.4** (Zermelo domain). *In every model of $B+\mathsf{US}_1$ there is a uniform transitive object $W$ with uniform members such that its first-member structure satisfies Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, Foundation, and every instance of full first-order Separation. In particular $W$ is hereditarily uniform.*

*Proof.* The formula

$$
\exists n,a\,(n\in_1\omega\land\operatorname{Stage}(n,a)\land x\in_1a)
$$

belongs to $L_1$ and its only needed parameters, zero and $\omega$, are uniform. Its prospective members are uniform by the stage argument. Hence Lemma [3.1](#lem:collection) produces a uniform object $W$ with exactly these members. In notation justified by the defining formula, its extension is

$$
W=\bigcup_{n\in\omega} A_n.
$$

This equation is an abbreviation for the first-extension formula, not an application of ambient Replacement or Union to a set of stages. Transitivity of each stage gives transitivity of $W$. Each stage $A_n$ is itself a member of $W$, since $A_n\in_1A_{S(n)}$ by the power definition and $A_n\subseteq_1A_n$. Thus $\omega\in_1W$ and $0\in_1W$. Moreover, if $a\in_1W$ and $b\subseteq_1a$, choose $n$ with $a\in_1A_n$; transitivity gives $b\subseteq_1A_n$, so $b\in_1A_{S(n)}$ and hence $b\in_1W$.

The structure whose domain is the first extension of $W$, with restricted first membership, satisfies Extensionality by transitivity and ambient First Extensionality, Empty Set by $0\in_1W$, and Infinity by $\omega\in_1W$. For Pairing, any two members of $W$ are uniform and belong to a common stage $A_n$. Their uniform unordered pair exists and is a subset of $A_n$, hence lies in $W$. For Union, if $a\in_1A_n$, every prospective member of its union lies in $A_n$ by transitivity and is uniform. The defining formula $\exists y\,(y\in_1a\land x\in_1y)$ yields a uniform union by Lemma [3.1](#lem:collection); its extension is contained in $A_n$, so it belongs to $W$. For Power Set, if $a\in_1A_n$, the uniform $b=\mathcal P_1(a)$ exists. Each $c\in_1b$ is a subset of $a$, hence a subset of $A_n$, so $c\in_1A_{S(n)}$. Consequently $b\in_1A_{S(S(n))}$ and lies in $W$. Transitivity ensures that subsethood computed inside $W$ is actual first-subsethood for its members, and the closure property just proved ensures all such subsets are present in $W$. Foundation follows by choosing a stage containing a given nonempty $a\in_1W$: then $a$ is a subset of that well-founded stage, so it has a minimal member, also in $W$.

Finally, let $\theta(x,\vec p)$ be any first-order formula of the ordinary set-theoretic language, and suppose $a$ and all components of $\vec p$ are first members of $W$. Relativize every quantifier of $\theta$ to the first members of $W$, translating membership by $\in_1$, to obtain an $L_1$-formula $\theta^W(x,\vec p)$. All parameters, including $a,W,\vec p$, are uniform. The formula $x\in_1a\land\theta^W(x,\vec p)$ defines only uniform objects. Lemma [3.1](#lem:collection) produces its first-extension representative $b$. Since $b\subseteq_1a$, it belongs to $W$. Induction on the syntax of the externally specified formula proves that $\theta^W$ expresses precisely its truth in the domain. This gives full Separation, with no boundedness restriction. All requested axioms have been verified. The witness $t=W$ in Definition [8.1](#def:hered) proves hereditary uniformity. ◻

<a id="rem:bounds"></a>

**Remark 8.5**. Theorem [8.4](#thm:zermelo) gives the external implication $\operatorname{Con}(B^+)\Rightarrow\operatorname{Con}(\mathsf{Z})$ by first-order completeness. Together with Theorem [7.1](#thm:rank), this places the extensions with uniform subsethood between Zermelo set theory and ZF in consistency strength. The lower bound uses satisfaction of each standard instance of Separation on the same domain $W$. An arithmetized proof of consistency inside $B^+$ would require a separate argument.

<a id="sec:lean"></a>

## 9. Formalization and verification boundary

The accompanying Lean 4 development formalizes the main model constructions. All 56 entries in the verification run’s source checksum manifest match the accompanying source snapshot. The recorded Git commit is

`4a170802b75462a01925b065e89c1ed5383af122`.

The recorded toolchain is Lean 4.36.0 with mathlib at revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The development encodes the object language of DEST by scoped first-order formulas. The axiom schemes of the theory in Section [2](#sec:axioms) range over that syntax. The older reference theory uses explicit least-inductive-set existence and induction on its members. The formal equivalences below identify it with the corresponding extension of the Infinity-free specification.

<a id="theorem-correspondence"></a>

### 9.1 Theorem correspondence

Table [1](#tab:formal) gives the main checked declarations. The mathematical reductions using the published metatheorems of Friedman and Kanovei–Lyubetsky are given in Sections [4](#sec:arith)–[6](#sec:exact).

<a id="tab:formal"></a>

| Mathematical result                         | Lean declaration and scope                                                                                                                                                                           |
|:--------------------------------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Original closed theory and derived Infinity | `DESTOriginalClosed.satisfies_iff_original` <br> `DESTOriginal.exists_uniform_omega` <br> Equivalence of the closed and semantic axiom formulations and derivation of a uniform least inductive set. |
| Arithmetic interpretation                   | `DESTOriginal.original_interprets_standard_arithmetic` <br> `DESTExact.parameter_free_from_original` <br> Functional arithmetic with parameter-free comprehension.                                   |
| Internal finite fragments                   | `DESTSet.finite_fragment_inside` <br> Carrier and second-membership graph inside models of the stated weak resources.                                                                                |
| First-language transfer                     | `DESTSet.first_sentence_of_internal_model` <br> Finite support and soundness for the declared reference calculus.                                                                                    |
| Compactness assembly                        | `DESTSet.reference_model_from_set_model` <br> Full reference model retaining a first-language sentence.                                                                                              |
| Exact strength                              | `DESTExact.z2_equiconsistency` <br> Conditional model-existence equivalence.                                                                                                                         |
| Uniform subsethood                          | `DESTRank.exists_SU_TI_model` <br> Model of $B+\mathsf{US}_1+\mathsf{TI}_1$ in the ambient type theory.                                                                                              |
| Zermelo domain                              | `DESTOriginal.exists_hereditarily_uniform_Z_model` <br> One hereditarily uniform transitive domain with full semantic Separation.                                                                    |

**Table 1.** Principal formal declarations and their mathematical scope.

The closed axiom schemes (B1)–(B5) are specified in `DEST/OriginalClosedSpecification.lean`. The semantic formulation, with $\mathsf{US}_1$ named `SU1` in the code, is in `DEST/OriginalSpecification.lean`. The equivalences with the reference theory are in `DEST/OriginalClosed.lean` and `DEST/OriginalStrength.lean`. In the weak-model development, `DEST/SetModel.lean` packages the set axioms and the definable least-witness order. The fragment theorem in `DEST/SetFragment.lean` uses the additional hypotheses of cofinal reflection and internal countability. It constructs both the carrier and a graph coding second membership as sets of the weak model. The compactness step is in `DEST/SetCompactness.lean`.

<a id="exact-meaning-of-the-conditional-theorem"></a>

### 9.2 Exact meaning of the conditional theorem

The module `DEST/ExactStrengthSpecification.lean` defines `Z2Satisfiable`, `OriginalSatisfiable`, and `InductiveSatisfiable` as existence of the corresponding first-order models in the ambient type theory. The theorem uses the following premises.

**`FriedmanRestriction`**. Existence of a parameter-free arithmetic model implies existence of a full Henkin arithmetic model.

**`ConstructibleInterpretation`**. Existence of a full Henkin arithmetic model implies existence of a weak set model satisfying the stated `CofinalReflection` and `InternallyCountable` resources, in addition to the fields of the weak-model structure.

Writing $\mathrm{FR}$ and $\mathrm{CI}$ for these two propositions, respectively, the checked statement in `DEST/ExactStrength.lean` is equivalent to

$$
\begin{gathered}
\mathrm{FR}\land\mathrm{CI}\quad\Longrightarrow\\[-1pt]
\Bigl[\bigl(\operatorname{Sat}(\mathsf{Z}_2)\leftrightarrow\operatorname{Sat}(B)\bigr)
\;\land\;
\bigl(\operatorname{Sat}(\mathsf{Z}_2)\leftrightarrow\operatorname{Sat}(T)\bigr)\Bigr].
\end{gathered}
$$

Both propositions are explicit premises of the checked Lean theorem. The written arguments in Sections [4](#sec:arith) and [5](#sec:upper) justify them using the cited metatheorems. The separate declaration `DESTExact.consistency_from_z2_model` yields syntactic consistency in the two declared DEST calculi from a Henkin model of $\mathsf{Z}_2$ and the constructible-interpretation premise. Classical first-order completeness gives the external equiconsistency statement from the semantic equivalence. The comparison of first-order arithmetic consequences is a result of the written proof, which uses the number-preservation argument of Lemma [5.1](#lem:arithmetic-preservation) in addition to model existence.

<a id="recorded-verification-evidence"></a>

### 9.3 Recorded verification evidence

The archived run reports ordinary Lean checking with `--trust=0` and comparison of 52 declarations with their frozen statements. The axiom audit records only `propext`, `Classical.choice`, and `Quot.sound`. Table [2](#tab:checks) gives the archived verdicts. The Comparator run used its sandbox. The exports and the direct replay checks were produced in the trusted checkout. The `con-leche` and `con-ron` logs describe their handling of the `Lean.Syntax` inductive block and the ordering of the `Nat.mul` records in the export.

<a id="tab:checks"></a>

| Verification stage                                         | Recorded verdict |
|:-----------------------------------------------------------|:-----------------|
| Ordinary Lean kernel and axiom audit                       | PASS             |
| Semantic audit, S1–S7                                      | PASS (7/7)       |
| Focused formal audit, F1–F3                                | PASS (3/3)       |
| Comparator + mathlib (statement match and axiom whitelist) | PASS             |
| leanchecker-paranoid                                       | PASS             |
| con-leche (verified mode)                                  | PASS             |
| con-ron (verified mode)                                    | PASS             |
| NanoDa + lean4lean                                         | PASS             |
| Exact Henkin model-existence equivalence                   | CONDITIONAL PASS |

**Table 2.** Verification results recorded for the pinned source snapshot.

The source contains the pinned dependencies, the statement comparison files `Challenge.lean` and `Solution.lean`, and the verification scripts. For replay instructions see `VERIFICATION.md` at the pinned commit. The evidence includes the theorem list, the run logs, the NDJSON exports, and checksum manifests for the exports, source files, and checker binaries. The manuscript reports the archived execution and a comparison of the supplied files with the recorded hashes. See ([12](#ref-lean), [13](#ref-mathlib)) for the underlying formalization systems.

<a id="conclusions"></a>

## 10. Conclusions

The matching construction isolates the condition that governs the upper bound. A requested extension defined with uniform parameters must either have a representative in the uniform region or contain the outside point assigned to it. Finite reflection gives precisely the supply of points needed to carry out both sides of the matching internally. This yields the arithmetic comparison even when first-membership set induction is imposed.

With uniform subsethood the uniform region must also be closed under first subsets. The rank-cut construction enforces this condition, while internally iterated powersets yield the Zermelo domain. The two arguments give the bounds of Sections [7](#sec:rank) and [8](#sec:zermelo). The exact strength with uniform subsethood is open in the present analysis.

<a id="code-and-verification-evidence-availability"></a>

## Code and verification evidence availability

The source is identified by the [pinned GitHub commit](https://github.com/zaljohar/Double-Extension/tree/4a170802b75462a01925b065e89c1ed5383af122) of the Double-Extension repository. See [GitHub Actions run 46033427790](https://github.com/zaljohar/Double-Extension/actions/runs/46033427790) for the archived check summaries. The run’s evidence artifact is subject to GitHub’s authentication and retention policies.

<a id="acknowledgments-and-disclosure-of-ai-use"></a>

## Acknowledgments and disclosure of AI use

The author formulated the variant studied here and directed the research. ChatGPT (OpenAI) assisted in developing proof strategies and arguments, identifying possible gaps, writing and debugging the Lean 4 formalization and verification scripts, consulting the literature, and drafting and editing the manuscript. The author is responsible for the mathematical claims, the interpretation of the verification evidence, and the final text.

## References

<a id="ref-kisielewicz89"></a>

**\[1\]** A. Kisielewicz, Double extension set theory, *Reports on Mathematical Logic* **23** (1989), 81–89.

<a id="ref-kisielewicz98"></a>

**\[2\]** A. Kisielewicz, A very strong set theory?, *Studia Logica* **61** (1998), 171–178. [doi:10.1023/A:1005048329677](https://doi.org/10.1023/A:1005048329677).

<a id="ref-holmes04"></a>

**\[3\]** M. R. Holmes, Paradoxes in double extension set theories, *Studia Logica* **77** (2004), 41–57. [Author’s manuscript](https://randall-holmes.github.io/Papers/nodouble.pdf).

<a id="ref-holmes05"></a>

**\[4\]** M. R. Holmes, The structure of the ordinals and the interpretation of ZF in double extension set theory, *Studia Logica* **79** (2005), 357–372. [doi:10.1007/s11225-005-3611-x](https://doi.org/10.1007/s11225-005-3611-x).

<a id="ref-friedman"></a>

**\[5\]** H. Friedman, On the necessary use of abstract set theory, *Advances in Mathematics* **41** (1981), 209–280. [doi:10.1016/0001-8708(81)90021-9](https://doi.org/10.1016/0001-8708(81)90021-9).

<a id="ref-gitman"></a>

**\[6\]** V. Gitman, Parameter-free schemes in second-order arithmetic, *Journal of Symbolic Logic*, First View (2025), 1–19. [doi:10.1017/jsl.2024.81](https://doi.org/10.1017/jsl.2024.81).

<a id="ref-kl"></a>

**\[7\]** V. Kanovei and V. Lyubetsky, Notes on the equiconsistency of ZFC without the Power Set axiom and second-order arithmetic, *Axioms* **14** (2025), 865. [doi:10.3390/axioms14120865](https://doi.org/10.3390/axioms14120865). The numbered results cited here refer to the expanded preprint [arXiv:2507.11643v4](https://arxiv.org/abs/2507.11643v4).

<a id="ref-kl2"></a>

**\[8\]** V. Kanovei and V. Lyubetsky, Constructibility in the Simpson set theory without the local countability axiom, *Mathematics* **14** (2026), 1499. [doi:10.3390/math14091499](https://doi.org/10.3390/math14091499).

<a id="ref-simpson"></a>

**\[9\]** S. G. Simpson, *Subsystems of Second Order Arithmetic*, 2nd ed., Cambridge University Press and Association for Symbolic Logic, 2009, Chapter VII.

<a id="ref-enderton"></a>

**\[10\]** H. B. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001.

<a id="ref-jech"></a>

**\[11\]** T. Jech, *Set Theory: The Third Millennium Edition, Revised and Expanded*, Springer, 2003.

<a id="ref-lean"></a>

**\[12\]** L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming language, in *Automated Deduction—CADE 28*, Lecture Notes in Computer Science 12699, Springer, 2021, 625–635. [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

<a id="ref-mathlib"></a>

**\[13\]** The mathlib Community, The Lean mathematical library, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, ACM, 2020, 367–381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).
