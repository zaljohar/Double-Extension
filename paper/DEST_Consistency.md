# Double Extension Set Theory: Derived Infinity, Arithmetic Strength, and Uniform Models of Zermelo Set Theory

**Zuhair Al-Johar**<sup>[†](#affiliation)</sup>

*27 November 2026*

## Abstract

We investigate Double Extension Set Theory (DEST), a first-order set theory with two extensional membership relations. Comprehension is unrestricted in the language of the first relation but specifies extensions with respect to the second. A uniformity scheme requires these extensions to coincide when the parameters are uniform and the object defined by comprehension is not a member of itself under the second relation. Relational natural-number induction suffices to derive the existence of a uniform least inductive set, all of whose members are uniform, without assuming an Infinity axiom. We establish equiconsistency with full second-order arithmetic in its first-order, two-sorted (Henkin) formulation and show that adding full first-membership set induction does not change this strength. The lower bound follows from an interpretation of parameter-free impredicative comprehension and Friedman's restriction theorem. For the upper bound, we construct finite-fragment models by an internal countable back-and-forth argument in the powerset-free constructible metatheory interpreted by Kanovei and Lyubetsky. The reductions also preserve first-order arithmetic consequences. With the additional axiom of uniform subsethood, we obtain an upper consistency bound from ZF and construct a single hereditarily uniform transitive set whose first-membership structure satisfies every axiom of Zermelo set theory, without assuming ambient set induction. We describe the accompanying Lean 4 formalization and distinguish its checked results from its explicit external metatheoretical premises.

**Keywords:** set theory; two membership relations; uniformity; second-order arithmetic; relative consistency; Zermelo set theory; formal verification.\
**2020 MSC:** 03E70, 03F35, 03B35, 03C15, 03E30.

# 1. Introduction

A comprehension principle need not assign the extension that it defines to the same membership relation used in the defining formula. Double Extension Set Theory (DEST) exploits this distinction. Its two relations, both extensional, play asymmetrical roles: the first determines the language of comprehension, whereas the second realizes the extension specified by comprehension. The uniformity scheme determines when the two extensions must agree. Thus unrestricted first-language comprehension does not entail unrestricted comprehension for the first membership relation.

The aim of this paper is to determine the arithmetic strength of a precise formulation of DEST without an Infinity axiom and to investigate the effect of uniform subsethood. The arithmetic comparison is with full second-order arithmetic as an effectively axiomatized first-order theory, not with categorical second-order semantics. The relevant background includes Friedman's work on parameter-free comprehension [1; 2], the set-theoretic interpretations of second-order arithmetic described by Simpson [3], and the explicit powerset-free interpretation of Kanovei and Lyubetsky [4; 5]. The present construction differs from those interpretations: it builds a second membership relation on an inherited first-membership domain and controls exactly the objects on which the relations agree.

Write $B$ for DEST with the axioms in Section [2](#sec:axioms), $T=B+\mathsf{TI}_1$, and $B^+ = B+\mathsf{US}_1$. Let $\mathsf{Z}$ denote Zermelo set theory with Foundation, Infinity and full Separation, but without Choice or Replacement. The principal conclusions are as follows.

<a id="thm:main"></a>
**Theorem 1.1** (Main results).

1.  *$B$ proves that there is a least inductive object $w$ such that both $w$ and all its first members are uniform.*

2.  *For every first-order arithmetic sentence $\sigma$, with its canonical von Neumann translation $\sigma^*$ into the first membership language, 

$$
\mathsf{Z}_2\vdash\sigma\quad\Longleftrightarrow\quad B\vdash\sigma^*
     \quad\Longleftrightarrow\quad T\vdash\sigma^*.
$$

 In particular, the external consistency statements are equivalent: 

$$
\operatorname{Con}(\mathsf{Z}_2)\;\Longleftrightarrow\;\operatorname{Con}(B)\;\Longleftrightarrow\;\operatorname{Con}(T).
$$

*

3.  *Externally, $\operatorname{Con}(\mathsf{ZF})\Longrightarrow\operatorname{Con}(B^+ + \mathsf{TI}_1)$.*

4.  *In every model of $B^+$ there is a single hereditarily uniform transitive object $W$ whose first-member structure satisfies $\mathsf{Z}$, including every instance of full Separation.*

Part (ii) uses number-domain preservation in the two published reductions, rather than merely their equiconsistency conclusions. Part (iii) is a finite-fragment relative-consistency argument; it is not a claim that ZF proves its own consistency or that a single interpretation has been formalized. Part (iv) asserts satisfaction of the axioms and axiom schemes at the semantic level; an internal satisfaction predicate for arbitrary formula codes is not part of that result. These distinctions are also relevant to the formalization in Section [9](#sec:lean).

<a id="sec:axioms"></a>
# 2. Language and axioms

The language $L$ has equality and two binary relation symbols $\in_1,\in_2$. Its first sublanguage $L_1$ contains only equality and $\in_1$. All structures have a nonempty domain. Variables range over the entire domain unless otherwise stated. The following are formula abbreviations, not additional primitive symbols: 

$$
\begin{aligned}
\operatorname{U}(a)&:\Longleftrightarrow\forall x\,(x\in_1a\leftrightarrow x\in_2a),\\
a\subseteq_1b&:\Longleftrightarrow\forall x\,(x\in_1a\to x\in_1b),\\
\operatorname{Zero}(z)&:\Longleftrightarrow\forall x\,\neg(x\in_1z),\\
\operatorname{Succ}(a,b)&:\Longleftrightarrow\forall x\,(x\in_1b\leftrightarrow(x=a\lor x\in_1a)),\\
\operatorname{Ind}(z,t)&:\Longleftrightarrowz\in_1t\land
 \forall a\,(a\in_1t\to\exists b\,(b\in_1t\land\operatorname{Succ}(a,b))),\\
\operatorname{N}_z(a)&:\Longleftrightarrow\forall t\,(\operatorname{Ind}(z,t)\to a\in_1t).
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

Throughout, $\mathsf{Z}_2$ is the two-sorted theory with number operations $0,S,+,\cdot$, the Peano equations, set extensionality, induction for all two-sorted formulas with parameters, and comprehension for every two-sorted formula, with number and set parameters. We do not add the countable-choice scheme. This presentation is equivalent to the customary full-comprehension theory with the usual arithmetical definitions [3]. Let $\mathsf{Z}_2^{\mathrm{pf}}$ have the same basic axioms but comprehension only for formulas without free set parameters; number parameters and bound set quantifiers are permitted. The parameter-free theory in Friedman's result can be taken with no free parameters other than the distinguished number variable; our comprehension suffices for that version as well.

<a id="sec:infinity"></a>
# 3. Uniform comprehension and derived Infinity

<a id="lem:collection"></a>
**Lemma 3.1** (Uniform collection). *Suppose $\varphi(x,\vec p)$ is an $L_1$-formula, each $p_i$ is uniform, and $\forall x(\varphi(x,\vec p)\to\operatorname{U}(x))$. There is a unique uniform object $a$ such that 

$$
\forall x\,(x\in_1a\leftrightarrow\varphi(x,\vec p)).
$$

 Its second extension is also given by $\varphi$.*

*Proof.* By (B3) take $a$ with the specified second extension. If $\neg\operatorname{U}(a)$, (B4) implies $\varphi(a,\vec p)$, whence $\operatorname{U}(a)$ by the hypothesis on the values of $\varphi$, a contradiction. Thus $a$ is uniform. First Extensionality gives uniqueness. ◻

The lemma is a derived scheme and is not the Collection scheme of ordinary set theory. Its hypotheses constrain the parameters and the prospective members, not the syntactic complexity of the first-language formula. In particular it yields a uniform empty object $z$ (using $x\ne x$) and uniform singletons and unordered pairs of uniform objects. For uniform $a,b$, the Kuratowski pair $\langle a,b\rangle=\{\{a\},\{a,b\}\}$ exists uniformly. The usual ordered-pair identity follows from First Extensionality: the intersection of the singleton and unordered-pair components identifies the first coordinate, and the members of their union identify the second coordinate once the first is known. This is an extensional argument about membership; it does not use a general Union axiom. If $g$ and each of its members are uniform, a uniform $p$ may be adjoined to it by the defining formula $x\in_1g\lor x=p$; the result again has uniform members.

<a id="thm:omega"></a>
**Theorem 3.2** (Infinity without an Infinity axiom). *$B$ proves the existence of a unique pair of objects $z,w$ such that $\operatorname{Zero}(z)$, $\operatorname{Ind}(z,w)$, and 

$$
\forall t\,(\operatorname{Ind}(z,t)\to w\subseteq_1t).
$$

 Moreover, $\operatorname{U}(w)$, $\forall x(x\in_1w\to\operatorname{U}(x))$, and $x\in_1w\leftrightarrow\operatorname{N}_z(x)$.*

*Proof.* Let $P(a)$ assert that $a$ and all its first members are uniform. By Lemma [3.1](#lem:collection), $z$ exists and $P(z)$ holds. Whenever $P(a)$ holds, apply the lemma to $x=a\lor x\in_1a$. It gives a uniform successor $b$ whose first members are uniform. Any other successor of $a$ equals $b$ by First Extensionality. Thus the induction step of (B5) holds for $P$, and $P(a)$ holds for every $a$ satisfying $\operatorname{N}_z(a)$.

Apply Lemma [3.1](#lem:collection) to the $L_1$-formula $\operatorname{N}_z(x)$ with uniform parameter $z$. This yields a uniform object $w$ with precisely these first members, each uniform. Every inductive object contains $z$, so $z\in_1w$. If $a\in_1w$, the preceding argument supplies its successor $b$. Every inductive object contains $a$ and has a successor of $a$ as a member. By functionality, that successor is $b$. Consequently $b\in_1w$. Therefore $w$ is inductive, and its defining equivalence makes it a subset of every inductive object. Uniqueness of $z$ and $w$ follows by extensionality. ◻

We henceforth write $\omega=w$, $0=z$, and $N(a)$ for $a\in_1\omega$. Induction on $N$ with arbitrary $L$-formulas and parameters follows immediately from (B5). The alternative axiom presentation with explicit existence of a least inductive object and induction on its members is deductively equivalent to $B$: Theorem [3.2](#thm:omega) proves its axioms from $B$; in the other direction, leastness gives the equivalence of $N$ and $\operatorname{N}_z$, hence (B5). This equivalence holds also after adding $\mathsf{TI}_1$ or $\mathsf{US}_1$.

<a id="sec:arith"></a>
# 4. Arithmetic internal to DEST

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

*Proof.* We use Friedman's restriction theorem [1 Lemma 3.1.7]; see also [2]. In the form required here, a countable model of parameter-free full second-order arithmetic admits a restriction of its set sort satisfying full second-order arithmetic, with its number structure unchanged. Our number-parameter comprehension includes the completely parameter-free instances required by that theorem. If $B\nvdash\sigma^*$, first-order completeness and downward Löwenheim--Skolem give a countable model of $B+\neg\sigma^*$. Theorem [4.3](#thm:pf) gives a countable parameter-free arithmetic model falsifying $\sigma$. Restrict its set sort using Friedman's theorem; the resulting full model still falsifies $\sigma$, a contradiction. ◻

<a id="sec:upper"></a>
# 5. The powerset-free upper bound

The construction in this section must be carried out within a weak set-theoretic metatheory, not merely in a stronger theory that proves the existence of a DEST model.

## 5.1 The interpreted metatheory and its resources

We use the interpretation of Kanovei and Lyubetsky [4], in particular Theorems 5.2 and 1.2 of the expanded preprint (version 4). Full second-order arithmetic without countable choice interprets their tree-based set theory $\mathsf{TMC}$; in it the constructible cut $L^*$ satisfies powerset-free ZFC with Collection. The cut is $L$ if the first uncountable ordinal of $L$ does not exist and $L_{\omega_1^L}$ otherwise. The distinction matters: one cannot simply assume the whole constructible universe satisfies Collection in the intermediate theory. The finite ordinals in the tree interpretation are the codes of the original numbers, and the cut is transitive and retains them. Consequently, the interpretation preserves first-order arithmetic, with addition and multiplication defined by the usual finite recursions. These features, rather than bare equiconsistency of the intermediate theories, are used below.

Write $\mathcal S$ for the interpreted structure. The internal proof requires the following resources.

**(R1)** Extensionality, Empty Set, Adjunction, Union, Infinity with a least inductive set $\omega$, Foundation, and full Separation and Collection for definable formulas. The usual set operations including finite Cartesian products are available.

**(R2)** A definable strict class order under which every nonempty definable class has a least element. The constructible order suffices: given a witness, its initial segment is bounded in a constructible level and Separation yields a set on which to take the least witness.

**(R3)** Cofinal finite reflection: for any set $a$ and any externally fixed finite family of definable requests $\chi_i(x,\vec p)$, there is a transitive set $d$ containing $a$ as a member, closed under adjunction, such that whenever all components of $\vec p$ are members of $d$ and a witness exists in $\mathcal S$, some witness belongs to $d$.

**(R4)** Internal countability: every nonempty set is the image of the internal $\omega$ under a surjection (equivalently, it admits an injection into $\omega$).

These are the resources encoded in the Lean weak-model specification. For (R3), apply the cofinal reflection result of [4 Corollary 8.4 and Lemma 8.5 in version 4] to the existential closures of the finitely many requests, expanding definable operations and relations, and choose a sufficiently large limit constructible level. Such a level is transitive and adjunction-closed. The order and Collection are supplied by Lemma 7.3 and Theorem 8.6 of the same reference. Internal countability of the cut is also explicit in [5 Lemmas 15 and 17(1)]. An enumeration is obtained from an injection by inverting it on its range and assigning a fixed member at other indices. No power set or set of all subsets is available or needed.

Every reference to a formula in the construction below denotes an externally fixed formula, with parameters varying over sets of $\mathcal S$. The interpretation and reflection facts can be applied separately to each such finite list. No truth predicate for the ambient universe is assumed. All set notation and internal induction in this section are interpreted in $\mathcal S$, including in nonstandard models. In particular, an internally finite history need not be finite externally.

<a id="sec:histories"></a>
## 5.2 Internal finite histories without Power Set

We record the set-existence argument used by the matching procedure. In powerset-free set theory with Collection, a definable functional relation on a set has a graph and a range: Collection gathers a set of witnesses, Separation removes extraneous witnesses, and the same argument applied to ordered-pair codes yields the graph. Finite products are obtained by collecting rows and taking unions. For an everywhere-defined functional update $h$ on states, define a history through $n$ to be a graph with domain $n+1$, a prescribed initial state, and consecutive values related by $h$. Start with a singleton history and extend it by one step by adjoining the next ordered pair. Internal induction gives existence at each internal $n$ and uniqueness by induction comparing two histories on their common domain. Collection gathers histories for all $n\in\omega$; Separation discards any extraneous objects that are not histories. The union of their compatible graphs gives a sequence. Equivalently, define the graph by the condition that an entry occurs in a history, then collect the ordered pairs and apply Separation. For a definable update specified by a finite case distinction, its graph is first-order definable. This is sufficient for all recursions below and requires no set of possible histories.

<a id="sec:regions"></a>
## 5.3 Reflecting domains and requested extensions

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
**Lemma 5.1** (Availability of fresh matches). *In the notation above the following statements hold.*

1.  *If $E\in J$ is protected, its defining class has no ambient representative, and $E\notin d$.*

2.  *Given any $b\in d$ and any protected $E\in J$, there exists $x\in E\cap O$ with $x\notin b$.*

3.  *For every $b\in d$ there exists $x\in O$ with $x\notin b$.*

4.  *For every $x\in O$, $\{x\}\in J$ and $\{x\}$ is not protected.*

*Proof.* (a) Take a protected definition $\varphi(x,\vec p)$ with parameters in $u$. If the ambient class has a representative $a$, the representative request in $u$ supplies one in $u$. By transitivity and [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"}, its extension equals $E$, contrary to $E\notin u$. If $E\in d$, an ambient disagreement between $E$ and the defining class would be witnessed in $d$, by the disagreement request with parameters $E,\vec p$. This contradicts the definition of $E$ and [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"}. Hence $E$ itself would be an ambient representative, which has just been ruled out.

\(b\) If no ambient $\varphi$-witness lay outside $u\cup b$, Separation on that union would represent the whole defining class. Thus a witness exists outside both sets. Since $u,b,\vec p\in d$, the outside request in $d$ supplies such a witness in $d$. By [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"} it belongs to $E$, and by construction it is outside $u$ and $b$.

\(c\) Apply the same argument to the formula that is always true: a set containing all sets would contain itself, contrary to Foundation. Thus there is an ambient witness outside $u\cup b$, and the true-formula outside request puts one in $d$.

\(d\) Transitivity of $u$ implies $\{x\}\notin u$, so it belongs to $J$. If it were protected, [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"} would give an ambient positive witness for its defining formula. The positive request in $u$ would supply a witness in $u$. That witness belongs to the singleton by [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"}, and must equal $x$, a contradiction. ◻

<a id="sec:matching"></a>
## 5.4 An internal back-and-forth

For $a\in O$ and $E\in J$, call $(a,E)$ admissible when 

<a id="eq:allowed"></a>

$$
a\ne E\quad\land\quad(E\text{ is protected}\;\to\;a\in E).\tag{5.2}
$$

 By Lemma [5.1](#lem:fresh)(c,d), both $O$ and $J$ are nonempty. They admit internal enumerations by (R4). We construct a bijection $f:O\to J$ whose graph consists of admissible matches. Each internally finite partial matching state includes a forbidden set $b\in d$ of used left points and singleton indices of any used singleton outputs from $O$. Start with the empty matching and the empty forbidden set. At each step, any additional forbidden points are in $d$, so adjunction closure keeps the forbidden set in $d$. For a used singleton output $\{x\}$, its index $x\in O$ is unique. Whether an output has this form is a definable test, and the set is updated accordingly.

For the next left point $a$, do nothing if it is matched. Otherwise choose an unused singleton output $\{x\}$ with $x\in O$ outside the forbidden set. Also exclude the unique possible $x$ such that $a=\{x\}$, by adjoining that index to the forbidden set if it lies in $d$. Lemma [5.1](#lem:fresh)(c,d) ensures the required singleton exists, is unprotected and belongs to $J$. The new pair is admissible.

For the next right point $E$, do nothing if it is already matched. Otherwise, if $E$ is protected, choose $a\in E\cap O$ outside the forbidden set by Lemma [5.1](#lem:fresh)(b); $a\ne E$ by (a). If $E$ is not protected, choose $a\in O$ outside the forbidden set, also excluding $E$ if $E\in d$. Lemma [5.1](#lem:fresh)(c) gives such an $a$. In either case the new pair is admissible. The update preserves injectivity and enlarges the matching, and updates the forbidden set to include the newly used points or singleton indices, as appropriate.

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

 The last equivalence follows from the fixed-point exclusion of [\[eq:allowed\]](#eq:allowed){reference-type="eqref" reference="eq:allowed"}. The construction is not an assignment of arbitrary subsets to objects, but a constrained bijection between internally collected families.

<a id="sec:verifyfrag"></a>
## 5.5 Axioms and preservation of arithmetic

<a id="thm:fragment"></a>
**Theorem 5.2** (Internal fragment model). *For every fixed finite family $Q$ of first-language defining formulas and every first-language sentence $s$, the resources (R1)--(R4) suffice to construct a set-coded structure $\mathcal D=(d,\in_1,\in_2)$ satisfying both extensionality axioms, comprehension and uniformity for $Q$, and every externally fixed instance of relational natural-number induction and first-membership set induction. Moreover, $\mathcal D\models s$ if and only if $\mathcal S\models s$.*

*Proof.* First Extensionality follows from transitivity of $d$; Second Extensionality from injectivity of $F$. Every requested extension is in $u$ or $J$, hence has a representative under $F$. This proves comprehension. Suppose the parameters of a requested instance of uniformity are uniform, and its extension is $E=F(a)$. By [\[eq:fixed\]](#eq:fixed){reference-type="eqref" reference="eq:fixed"}, the parameters lie in $u$, so $E$ is protected. If $a\notin u$, admissibility implies $a\in E$, i.e. $a\in_2a$. Therefore the non-self-membership premise forces $a\in u$, which is precisely uniformity.

The empty object, all the internal numbers of $\mathcal S$, and its least inductive set $\omega$ belong to $d$. The successors of these numbers are present in $d$; the restricted successor relation agrees with the ambient one, because of transitivity and extensionality. The inherited $\omega$ is inductive. For any object $t$ that is inductive in $d$, internal induction in $\mathcal S$ proves that it contains every number: the base follows from inductiveness, and any successor witness in $d$ must be the actual successor. Hence $\omega$ is the least inductive object of $\mathcal D$. The domain defined by $\operatorname{N}_z$ in (B5) therefore agrees exactly with the internal numbers of $\mathcal S$. For any fixed induction formula, relativize its quantifiers to $d$ and replace second membership by the definable relation [\[eq:relations\]](#eq:relations){reference-type="eqref" reference="eq:relations"}. This is a formula in $\mathcal S$, so its natural-number induction applies and verifies (B5). For $\mathsf{TI}_1$, separate the set of counterexamples inside $d$. If it is nonempty, it has a membership-minimal element by ambient Foundation. This contradicts progressiveness, since the inherited relation is ambient membership restricted to $d$. These arguments allow arbitrary parameters and both membership symbols. Finally, $s$ is first-language, so [\[eq:reflect\]](#eq:reflect){reference-type="eqref" reference="eq:reflect"} gives its preservation independently of $F$. ◻

**Remark 5.3** (Why this is a weak-metatheory construction). Only extensions of fixed formulas over specified sets are collected. The fresh-witness argument uses nonrepresentability and Separation, not a cardinality estimate for an ambient proper class. The matching uses set-coded enumerations and internally finite histories, not external choice or a set of all partial maps. The graph of second membership and the induction counterexamples are sets of the weak model. These facts are necessary to apply internal Foundation and induction. Merely showing that a matching exists externally would not suffice.

<a id="sec:exact"></a>
# 6. Exact arithmetic strength

<a id="thm:upper"></a>
**Theorem 6.1** (Upper bound and arithmetic preservation). *For any first-order arithmetic sentence $\sigma$, if $T\vdash\sigma^*$ then $\mathsf{Z}_2\vdash\sigma$. Also, any Henkin model of $\mathsf{Z}_2$ yields, externally, a model of $T$.*

*Proof.* Fix a finite derivation of $\sigma^*$ in $T$. There are finitely many comprehension and uniformity formulas in it; let $Q$ contain them. Choose $s=\sigma^*$ in Theorem [5.2](#thm:fragment). Given any model of $\mathsf{Z}_2$, apply the published tree interpretation and pass to the constructible cut to obtain a weak set model with (R1)--(R4). The theorem gives an internal model of the finite axiom support of the derivation, retaining the truth of $s$. Ordinary soundness applied to that finite derivation yields $\mathcal D\models\sigma^*$, so $\mathcal S\models\sigma^*$. In $\mathcal S$ the translation of arithmetic is the ordinary von Neumann arithmetic: zero, successor and least inductive object are the standard internal definitions, and the recursion graphs define the ordinary addition and multiplication by their unique recursion values. Preservation of the number domain under the published interpretation therefore implies that the original arithmetic model satisfies $\sigma$. Since the model of $\mathsf{Z}_2$ was arbitrary, first-order completeness gives $\mathsf{Z}_2\vdash\sigma$.

For the second assertion, start with any model of $\mathsf{Z}_2$ and its interpreted weak set model. Every externally specified finite subset of $T$ has a model by Theorem [5.2](#thm:fragment), taking $s$ to be a logical truth. Classical first-order compactness (see [7]), used externally, supplies one model of $T$. This step does not assert that the interpreted weak theory proves a single internal truth predicate for all fragments, nor that $\mathsf{Z}_2$ proves $\operatorname{Con}(T)$. ◻

<a id="cor:exact"></a>
**Corollary 6.2** (Equiconsistency and equal arithmetic consequences). *For every first-order arithmetic sentence $\sigma$, 

$$
\mathsf{Z}_2\vdash\sigma\quad\Longleftrightarrow\quad B\vdash\sigma^*
\quad\Longleftrightarrow\quad T\vdash\sigma^* .
$$

 In particular, $\operatorname{Con}(\mathsf{Z}_2)\leftrightarrow\operatorname{Con}(B)\leftrightarrow\operatorname{Con}(T)$.*

*Proof.* Combine Corollary [4.4](#cor:lower), the inclusion $B\subseteq T$, and Theorem [6.1](#thm:upper). For the consistency equivalences one may either use an arithmetic contradiction in the comparison, or combine the model transformations, Friedman's restriction and first-order completeness. No form of uniform subsethood is used in this argument. ◻

The consistency statements are external metamathematical comparisons of recursively specified first-order theories. They assert neither validity under full second-order semantics nor that one of the theories proves its own consistency. The number-preserving versions of the published reductions are necessary for the stronger arithmetic assertion; plain equiconsistency would suffice only for the weaker conclusion.

<a id="sec:rank"></a>
# 7. Uniform subsethood and a ZF relative-consistency bound

The additional principle $\mathsf{US}_1$ requires every object whose first extension is contained in a uniform object's first extension to be uniform. The preceding powerset-free construction does not automatically enforce this condition: its uniform region must be changed to one with an appropriate subset-closure property. We give a separate finite-fragment argument over ZFC, then pass to ZF through constructibility.

<a id="thm:rank"></a>
**Theorem 7.1**. *If ZF is consistent, then $B+\mathsf{US}_1+\mathsf{TI}_1$ is consistent.*

*Proof.* Work first in ZFC, and fix an externally specified finite fragment of the displayed theory. Let $Q$ contain the finitely many first-language formulas in its uniformity instances. For each $\varphi(x,\vec p)\in Q$, include in a finite reflection family $\varphi$, the positive-witness formula $\exists x\,\varphi(x,\vec p)$, the representative formula 

$$
R_\varphi(a,\vec p):\Longleftrightarrow\forall x\,(x\in a\leftrightarrow\varphi(x,\vec p)),
$$

 and $\exists a\,R_\varphi(a,\vec p)$, together with the required subformulas. By finite Lévy--Montague reflection (see [6]), choose limit ordinals $\omega<\alpha<\beta$ such that $V_\alpha$ and $V_\beta$ agree on these formulas for parameters in $V_\alpha$. Both levels are transitive. Choose a countable elementary substructure $M$ of $(V_\beta,\in,V_\alpha)$, where the last entry is a unary predicate, containing $\omega$ and every finite ordinal. Put $U=M\cap V_\alpha$.

For $a\in M$ let $E(a)=\{x\in M:x\in a\}$. By elementarity and ambient Extensionality, the map $a\mapsto E(a)$ is injective. Let $D$ be the family of all subsets of $M$ definable in the first language with parameters from $M$. It is countable, since the language and $M$ are countable. It contains $E(a)$ for all $a\in M$ and all singletons of members of $M$. Prescribe $F(a)=E(a)$ for $a\in U$. Call $C\in D$ protected if some formula in $Q$ defines $C$ over $M$ with parameters from $U$.

We verify the matching conditions, now in terms of traces. Suppose $C$ is protected, defined by $\varphi(x,\vec p)$ with $\vec p\in U$. Write $C^*=\{x\in V_\beta:V_\beta\models\varphi(x,\vec p)\}$. If $C^*$ has a representative in $V_\beta$, reflection supplies a representative in $V_\alpha$ and elementarity in the expanded language supplies one in $U$. Its trace is $C$. Conversely, if $C=E(a)$ for $a\in M$, elementarity makes $a$ a representative of $C^*$ in $V_\beta$; the preceding argument and trace injectivity imply $a\in U$. Thus, a protected extension not already fixed has no representative in $V_\beta$.

In this last case $C^*$ is unbounded in rank below $\beta$: any subset of $V_\beta$ of bounded rank is an element of $V_\beta$, since $\beta$ is limit. Hence $C^*$ has arbitrarily many points outside $V_\alpha$. By elementarity with the extra predicate, $C$ contains arbitrarily many points of $M\setminus U$, avoiding any prescribed finite list of elements of $M$. There are also arbitrarily many points of $M\setminus U$ without any condition on membership in $C$, by the same elementarity argument applied to the ranks between $\alpha$ and $\beta$.

For $b\in M\setminus U$, the singleton $\{b\}$ is not a fixed trace: a representative from $U$ would, by elementarity, have $b$ as an actual member, contradicting transitivity of $V_\alpha$. Nor is it protected. If it were defined by a formula from $Q$ with parameters in $U$, positive-witness reflection to $V_\alpha$, followed by elementarity in the expanded language, would produce a member of $U$ in that singleton.

Complete the prescribed assignments by the countable back-and-forth used in Section [5.4](#sec:matching), with left domain $M\setminus U$, right domain $D\setminus\{E(a):a\in U\}$, and admissibility condition 

$$
E(a)\ne C\quad\land\quad(C\text{ is protected}\;\to\;a\in C).
$$

 For an unmatched left point, use a fresh unprotected singleton, avoiding its first trace. For an unmatched right point, use a fresh member outside $U$ of the extension if it is protected (its trace cannot equal that extension), and otherwise any fresh outside point avoiding the at most one point with that trace. The properties just proved ensure all choices. This produces a bijection $F:M\to D$ such that $F(a)=E(a)$ exactly on $U$.

Let $x\in_1a$ mean $x\in a$ in the inherited structure and $x\in_2a$ mean $x\in F(a)$. Both Extensionalities hold, and surjectivity realizes comprehension. Uniform objects are precisely $U$, and the protected-extension condition gives all requested uniformity instances, as in Theorem [5.2](#thm:fragment).

To verify $\mathsf{US}_1$, suppose $a\in U$ and the first trace of $b$ is included in that of $a$. Elementarity implies $V_\beta\models b\subseteq a$, hence $b\subseteq a$ in the ambient universe by transitivity. Since $a\in V_\alpha$, rank monotonicity for subsethood gives $b\in V_\alpha$, so $b\in U$. This is precisely $\mathsf{US}_1$. The first relation is well-founded in the ambient metatheory, so every instance of $\mathsf{TI}_1$ holds, even for formulas involving the second relation. The included finite ordinals and $\omega$ give the least inductive object and natural-number induction as before (here the internal naturals are the actual naturals of the ambient construction).

Thus, each specified finite fragment has a model in ZFC. For ZF, perform this fixed-fragment argument in the constructible universe $L$, which satisfies ZFC. The resulting set structure satisfies the specified fragment also in the surrounding universe, by absoluteness of satisfaction for fixed first-order formulas in set structures. Equivalently, any model of ZF admits the corresponding interpreted construction in its $L$. If ZF is consistent, first-order completeness and external compactness therefore give the asserted consistency. No single truth predicate for all fragments, inaccessible cardinal, or internal proof of $\operatorname{Con}(\mathsf{ZF})$ is used. ◻

The corresponding Lean theorem constructs a model of $B+\mathsf{US}_1+\mathsf{TI}_1$ in its ambient set-theoretic development, using a rank cut of `ZFSet` closed under witness queries. The finite-reflection proof above is the external reduction to ZF. In particular, the theorem does not constitute an encoded interpretation of the entire extended DEST theory in ZF.

<a id="sec:zermelo"></a>
# 8. A hereditarily uniform Zermelo domain

We now work in an arbitrary model of $B^+ = B+\mathsf{US}_1$, without assuming $\mathsf{TI}_1$. All membership and subsethood notation in this section refers to $\in_1$. For clarity the subscript is retained in the principal formulas. A set is transitive if every first member of a first member is also a first member of the set. A set $a$ is well-founded on its members if every nonempty object $b\subseteq_1a$ has a member with no first member in $b$.

<a id="def:hered"></a>
**Definition 8.1**. An object $a$ is hereditarily uniform if $\operatorname{U}(a)$ and there is a transitive $t$ with $a\subseteq_1t$ and $\forall x(x\in_1t\to\operatorname{U}(x))$.

This witness formulation is equivalent to the existence of a least transitive superset of $a$ with uniform members, together with $\operatorname{U}(a)$. Indeed, given a witness $t$, form the intersection of all transitive supersets of $a$, using the first-language formula for membership in that intersection with uniform parameter $a$. Its values are members of $t$ and hence uniform, so Lemma [3.1](#lem:collection) applies. The resulting intersection is transitive, contains $a$ as a subset, and is the least such superset. A transitive uniform object with uniform members is itself such a witness.

<a id="lem:powerset"></a>
**Lemma 8.2** (Uniform powersets). *For every uniform $a$, there is a unique uniform $b=\mathcal P_1(a)$ with uniform members such that 

$$
x\in_1b\quad\Longleftrightarrow\quad x\subseteq_1a.
$$

 If $a$ is transitive and well-founded on its members, then so is $b$.*

*Proof.* By $\mathsf{US}_1$, all prospective members of the first-language subset formula with parameter $a$ are uniform. Lemma [3.1](#lem:collection) gives the asserted $b$. For transitivity, if $y\in_1x\in_1b$, then $y\in_1a$, and since $a$ is transitive, $y\subseteq_1a$, so $y\in_1b$. Also, $a\subseteq_1b$ by transitivity of $a$.

For well-foundedness let $d\subseteq_1b$ be nonempty. It is uniform by $\mathsf{US}_1$. Every member of $a$ is a subset of $a$ by transitivity, hence is uniform by $\mathsf{US}_1$. If $d$ has a member in $a$, the nonempty intersection $e=d\cap a$ exists by Lemma [3.1](#lem:collection), since its parameters and prospective members are uniform. Choose a minimal member $x$ of $e$ using well-foundedness of $a$. Any first member of $x$ belonging to $d$ belongs to $a$ by transitivity, and so belongs to $e$, a contradiction. If $d$ has no member in $a$, every member $x$ of $d$ is minimal in $d$: all its first members lie in $a$, since $x\in_1b$. This proves the result. ◻

<a id="lem:omega-good"></a>
**Lemma 8.3**. *The object $\omega$ is uniform, transitive, has uniform members, and is well-founded on its members.*

*Proof.* Uniformity is Theorem [3.2](#thm:omega); transitivity is Lemma [4.1](#lem:numbers). Let $d\subseteq_1\omega$ be a nonempty object without a minimal member. Induct on numbers $n$ in the assertion that $n\notin_1 d$ and no member of $n$ belongs to $d$. The base follows from emptiness of zero and the assumption that $d$ has no minimal member. If the assertion holds at $n$, no member of $S(n)$ belongs to $d$. Were $S(n)$ itself in $d$, it would be minimal. Thus the assertion holds at the successor. It follows that $d$ has no member, a contradiction. This uses (B5), with parameter $d$, not ambient set induction. ◻

## 8.1 Internal powerset stages

For every internal number $n$, we define a stage $A_n$ by an internal recursion satisfying 

<a id="eq:stages"></a>

$$
A_0=\omega,\qquad A_{S(n)}=\mathcal P_1(A_n).\tag{8.1}
$$

 We must establish a single first-language stage relation, not just construct an external sequence for the standard numbers. Let $\operatorname{Stage}(n,a)$ assert that there exists a first-membership graph with natural-number indices through $n$, initial value $\omega$, and transitions given by the first-language power relation 

$$
\operatorname{Power}(v,w):\Longleftrightarrow\forall y\,(y\in_1w\leftrightarrow y\subseteq_1v),
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

**Remark 8.5**. The result asserts that each model of $B^+$ contains a single object whose first-member structure satisfies all ordinary Zermelo axioms and every instance of its axiom schemes. It does not identify an internal arithmetized satisfaction predicate for all internally coded formulas. Establishing such a predicate and deriving an arithmetized consistency statement inside $B^+$ using it is a distinct formalization problem. No ambient Foundation or $\mathsf{TI}_1$ is used to obtain the domain, and the result makes no claim of an exact consistency strength for $B^+$.

<a id="sec:lean"></a>
# 9. Formalization and verification boundary

The accompanying Lean 4 source archive formalizes the constructions described above. The source snapshot and the latest verification evidence supplied with the manuscript agree on all entries of the source checksum manifest. The recorded Git commit is

`4a170802b75462a01925b065e89c1ed5383af122`.

The recorded toolchain is Lean 4.36.0 with mathlib at revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Lean and mathlib provide the ambient formal language and the model-theoretic infrastructure; the object language of DEST is independently encoded by scoped first-order syntax, and its axiom schemes range over that syntax rather than arbitrary predicates of Lean. This distinction is essential for a semantic audit of comprehension and induction.

## 9.1 Theorem correspondence

Table [1](#tab:formal) records the main checked endpoints. We distinguish model-existence theorems in the ambient type theory from external reductions of consistency strength. In particular, the formal theorem for the Zermelo domain quantifies over every first-language Separation formula, and the weak-model construction uses internally coded matching histories rather than merely an external countable enumeration.

<a id="tab:formal"></a>

| Mathematical result | Lean declaration and scope |
|---|---|
| Original closed theory and derived Infinity | `DESTOriginalClosed.Satisfies`; `DESTOriginal.exists_uniform_omega`. The original specification contains no Infinity axiom. |
| Arithmetic interpretation | `DESTOriginal.original_interprets_standard_arithmetic`; `DESTExact.parameter_free_from_original`. Functional arithmetic with parameter-free comprehension. |
| Internal finite fragments | `DESTSet.finite_fragment_inside`. Carrier and second-membership graph inside models of the stated weak resources. |
| First-language transfer | `DESTSet.first_sentence_of_internal_model`. Finite support and soundness for the declared reference calculus. |
| Compactness assembly | `DESTSet.reference_model_from_set_model`. Full reference model retaining a first-language sentence. |
| Exact strength | `DESTExact.z2_equiconsistency`. Conditional model-existence equivalence. |
| Uniform subsethood | `DESTRank.exists_SU_TI_model`. Ambient semantic existence, not an encoded ZF proof transformation. |
| Zermelo domain | `DESTOriginal.exists_hereditarily_uniform_Z_model`. One hereditarily uniform transitive domain with full semantic Separation. |

*Table 1: Principal formal declarations and their mathematical scope.*

The file `DEST/OriginalClosedSpecification.lean` independently specifies the original axioms. The equivalences to the earlier reference theory, including the derived Infinity axiom, are in `DEST/OriginalClosed.lean` and `DEST/OriginalStrength.lean`. The weak-model development is in `DEST/SetLanguage.lean` through `DEST/SetFragment.lean`, with the compactness assembly in `DEST/SetCompactness.lean`. In that development, the set operations, Separation and Collection are fields of a weak-model structure. Definability in its first-order language is tracked explicitly. The reflection hypothesis supplies transitive adjunction-closed regions; internal countability supplies enumeration graphs. These two resource conditions are hypotheses of the internal fragment theorem. The theorem then constructs the carrier and the second membership graph as sets of that model. It is stronger than a construction solely in mathlib's ambient `ZFSet`.

## 9.2 Exact meaning of the conditional theorem

The module `DEST/ExactStrengthSpecification.lean` defines `Z2Satisfiable`, `OriginalSatisfiable`, and `InductiveSatisfiable` as existence of the corresponding first-order models in the ambient type theory. Its two external propositions are:

**`FriedmanRestriction`.** Existence of a parameter-free arithmetic model implies existence of a full Henkin arithmetic model.

**`ConstructibleInterpretation`.** Existence of a full Henkin arithmetic model implies existence of a weak set model satisfying the stated `CofinalReflection` and `InternallyCountable` resources, in addition to the fields of the weak-model structure.

Writing $\mathrm{FR}$ and $\mathrm{CI}$ for these two propositions, respectively, the checked statement in `DEST/ExactStrength.lean` is equivalent to 

$$
\begin{gathered}
\mathrm{FR}\land\mathrm{CI}\quad\Longrightarrow\\[-1pt]
\Bigl[\bigl(\operatorname{Sat}(\mathsf{Z}_2)\leftrightarrow\operatorname{Sat}(B)\bigr)
\;\land\;
\bigl(\operatorname{Sat}(\mathsf{Z}_2)\leftrightarrow\operatorname{Sat}(T)\bigr)\Bigr].
\end{gathered}
$$

 The external propositions are explicit arguments of the theorem, not new foundational axioms admitted by the checker. The mathematical argument for discharging those premises uses the published results cited in Sections [4](#sec:arith) and [5](#sec:upper). The separate formal theorem `DESTExact.consistency_from_z2_model` yields syntactic consistency of the two declared DEST calculi from a Henkin model of $\mathsf{Z}_2$ and the constructible-interpretation premise. Ordinary first-order completeness externally relates the model-existence equivalence to the usual equiconsistency statement. The stronger number-preserving comparison in Corollary [6.2](#cor:exact) is the mathematical argument in this paper; it is not itself the exact type of `DESTExact.z2_equiconsistency`.

## 9.3 Recorded verification evidence

The latest evidence archive records 52 Comparator declaration targets. It reports successful ordinary Lean checking with `--trust=0`, semantic checks S1--S7, focused checks F1--F3, and the formal-strength audit including the conditional result. The five supplementary verification stages reported in the archive are listed in Table [2](#tab:checks). The Comparator sandbox was enabled in that run. The recorded axiom audit reports only the foundational dependencies `propext`, `Classical.choice`, and `Quot.sound`; the explicit hypotheses of the exact-strength theorem remain unchanged.

<a id="tab:checks"></a>

| Verification stage | Recorded verdict |
|---|---|
| Ordinary Lean kernel and axiom audit | PASS |
| Semantic audit, S1–S7 | PASS (7/7) |
| Focused formal audit, F1–F3 | PASS (3/3) |
| Comparator + mathlib (statement match and axiom whitelist) | PASS |
| leanchecker-paranoid | PASS |
| con-leche (verified mode) | PASS |
| con-ron (verified mode) | PASS |
| NanoDa + lean4lean | PASS |
| Exact Henkin model-existence equivalence | CONDITIONAL PASS |

*Table 2: Recorded verification results in the supplied evidence archive. These are not a new independent execution of the checkers.*

For reproduction, the source archive contains `lean-toolchain`, `lake-manifest.json`, `comparator.json`, `Challenge.lean`, `Solution.lean`, the specification and baseline checksum manifests, and the verification scripts. The evidence archive includes the run logs, source and tool-binary manifests, theorem targets, and exported NDJSON proof objects. The checksums of the recorded proof exports and source files were checked during manuscript preparation. A fresh execution of the verification workflow was not performed as part of manuscript preparation. The source and verification archives together provide the material needed to reproduce the checks and inspect the specifications, external premises, and trusted infrastructure. See [8; 9] for the underlying formalization systems.

# 10. Conclusions

The asymmetry between the two membership relations permits unrestricted first-language comprehension for second extensions while enforcing coincidence on a controlled uniform domain. The relational induction scheme suffices to derive a uniform least inductive set. Uniform collection then realizes the full parameter-free arithmetic comprehension scheme without requiring the second sort itself to consist of uniform objects. The finite-fragment matching construction shows that even full first-membership set induction can be realized in a powerset-free constructible metatheory of the arithmetic strength of $\mathsf{Z}_2$. Together, these two directions establish the exact comparison in Theorem [1.1](#thm:main)(ii).

Uniform subsethood imposes an additional closure condition on the uniform domain. A rank cut provides the ZF relative-consistency bound, and the additional powerset operation yields a hereditarily uniform Zermelo domain by internal finite recursion. The exact consistency strength of DEST with uniform subsethood remains undetermined. Although the construction gives a single domain satisfying all the axioms of Zermelo set theory, deriving an internal arithmetized consistency statement for that theory remains a separate question.

# Code and verification evidence availability

The Lean source code is available in the public GitHub repository at:

<https://github.com/zaljohar/Double-Extension/tree/chatgptwork-consistency>

The exact source snapshot is identified by the [Git commit recorded in Section 9](https://github.com/zaljohar/Double-Extension/tree/4a170802b75462a01925b065e89c1ed5383af122). The corresponding verification workflow and its logs are available at:

<https://github.com/zaljohar/Double-Extension/actions/runs/46033427790>

The evidence archive can be downloaded from the Artifacts section of the workflow summary, subject to GitHub's authentication and artifact-retention policies.

# Declaration of generative AI use and contribution

The author formulated Double Extension Set Theory and directed the research objectives and revisions. ChatGPT (OpenAI), a generative AI system, was used extensively as a research assistant in the development of this work. Its contributions included proposing and developing mathematical proof strategies, deriving and refining arguments, identifying potential gaps, generating and revising Lean 4 formalizations, assisting with debugging and the verification workflow, consulting relevant literature, and drafting and editing the manuscript. Its role therefore extended beyond language editing to substantive assistance with the mathematical proofs and their formalization. The formal verification claims are based on the recorded checker evidence described in Section [9](#sec:lean), not on assurances by the AI system; the external metatheoretical premises remain explicit. ChatGPT is not an author and does not bear responsibility for the work. Responsibility for the correctness, originality, interpretation, and final submitted content rests with the human author.

# References

1. H. Friedman, On the necessary use of abstract set theory, *Advances in Mathematics* **41** (1981), 209--280. [doi:10.1016/0001-8708(81)90021-9](https://doi.org/10.1016/0001-8708(81)90021-9).

2. V. Gitman, Parameter-free schemes in second-order arithmetic, *Journal of Symbolic Logic*, published online 2024. [doi:10.1017/jsl.2024.81](https://doi.org/10.1017/jsl.2024.81).

3. S. G. Simpson, *Subsystems of Second Order Arithmetic*, 2nd ed., Cambridge University Press and Association for Symbolic Logic, 2009, Chapter VII.

4. V. Kanovei and V. Lyubetsky, Notes on the equiconsistency of ZFC without the Power Set axiom and second-order arithmetic, *Axioms* **14** (2025), 865. [doi:10.3390/axioms14120865](https://doi.org/10.3390/axioms14120865). Expanded preprint, [arXiv:2507.11643v4](https://arxiv.org/abs/2507.11643v4); theorem and lemma numbers cited in this paper refer to that version.

5. V. Kanovei and V. Lyubetsky, Constructibility in the Simpson set theory without the local countability axiom, *Mathematics* **14** (2026), 1499. [doi:10.3390/math14091499](https://doi.org/10.3390/math14091499).

6. T. Jech, *Set Theory: The Third Millennium Edition, Revised and Expanded*, Springer, 2003.

7. H. B. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001.

8. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming language, in *Automated Deduction---CADE 28*, Lecture Notes in Computer Science 12699, Springer, 2021, 625--635. [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

9. The mathlib Community, The Lean mathematical library, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, ACM, 2020, 367--381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).


<a id="affiliation"></a>

<sup>†</sup> University of Baghdad.
