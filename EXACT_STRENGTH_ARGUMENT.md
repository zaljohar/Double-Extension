# Exact arithmetic strength of corrected DEST: mathematical proof using published reductions

**Lean update.** `DESTSet.finite_fragment_inside` formalizes the fixed-fragment
construction in an arbitrary weak set model with the resources of the
constructible cut. `DESTSet.reference_model_from_set_model` applies compactness,
and `DESTExact.z2_equiconsistency` proves the full model-existence equivalence
with both published reductions as explicit hypotheses. `WEAK_METATHEORY.md`
gives the detailed fixed-fragment argument behind Section 3.

## Status and scope

The mathematical argument below also treats the stronger equality of
arithmetic consequences. The Lean theorem certifies the conditional Henkin
model-existence equivalence. Classical first-order completeness gives its
ordinary external equiconsistency reading.

Write B for original corrected DEST, **without an Infinity axiom** and without
SU or TI. Use the relational natural-number induction scheme in
`DEST/OriginalClosedSpecification.lean`, stated below. Write T for B plus
full first-membership set induction. Z2 means classical two-sorted full
second-order arithmetic as a recursively axiomatized first-order theory with
Henkin models, with full comprehension and without requiring countable choice.
The theorem is not about full second-order validity.

**Claim.** For each first-order arithmetic sentence s, under the fixed
von Neumann arithmetic translation s*,

    Z2 |- s  iff  B |- s*  iff  T |- s*.

Consequently the theories are equiconsistent, and if Z2 is consistent neither
B nor T proves its arithmetized consistency under that translation.

The proof below uses classical first-order completeness and two published
model/interpretation theorems, not unproved consistency assumptions.

## 1. Published reductions used

1. Harvey Friedman, *On the necessary use of abstract set theory*, Advances
   in Mathematics 41 (1981), 209–280, Lemma 3.1.7:
   https://doi.org/10.1016/0001-8708(81)90021-9 . Given a countable model of
   parameter-free full second-order arithmetic, its set domain can be
   restricted to obtain a model of full second-order arithmetic with the
   same number structure. See Victoria Gitman, *Parameter-free schemes in
   second-order arithmetic*, exposition of the lemma and its arithmetic
   domain: https://victoriagitman.github.io/publications/2024/01/18/parameter-free-schemes-in-second-order-arithmetic.html .
2. Vladimir Kanovei and Vassily Lyubetsky, *Notes on the Equiconsistency of
   ZFC Without the Power Set Axiom and Second-Order Arithmetic*, Axioms 14
   (2025), 865, https://doi.org/10.3390/axioms14120865 . The accessible v4
   preprint is https://arxiv.org/html/2507.11643v4 . Theorems 5.2 and 1.2
   there interpret the tree theory TMC in full second-order arithmetic without
   countable choice, and interpret powerset-free ZFC in TMC by the constructible
   cut L*. Use this cut, not the whole constructible universe indiscriminately.
   Definition 8.1, Lemma 8.2, Lemma 7.3 and Theorem 8.6 supply the local
   countability and definable well-order used below. Internal countability of
   the cut in both cases is explicit in Lemmas 15 and 17(1) of their
   [2026 follow-up](https://doi.org/10.3390/math14091499). A nonempty set has
   an enumeration by taking the inverse of its injection into omega on the
   range and using one member as the default elsewhere. Corollary 8.4 and
   Lemma 8.5 of the 2025 paper supply finite reflection, also for formulas
   using the definable well-order and adjunction. Every initial segment of the canonical global well-order
   lies in a constructible level in the cut. Thus we may take S to be ZFC
   without Power Set, with Collection, well-orderability, every set countable
   and V=L. The tree interpretation identifies the number domain with the
   finite-ordinal codes, and the transitive constructible cut preserves those
   numbers and arithmetic. This supplies the arithmetic-preserving reduction
   used in Section 3. Compare Simpson, *Subsystems of Second Order Arithmetic*,
   Chapter VII. In the 2025 paper, PA2-minus is the theory denoted here by Z2;
   their PA2 additionally includes countable choice.

We use the actual interpretation and number-domain preservation in both
reductions. An appeal to equiconsistency alone would not prove the claim.

## 1A. Infinity is a theorem, not an axiom

Let m and r be the two memberships. First-language successor S(a,b) means
`forall y, m(y,b) iff (y=a or m(y,a))`. An inductive object is an object
containing zero and closed under this relation with witnesses inside itself.
For an empty object z define N_z(a) to mean that a belongs to every inductive
object based at z. This is a first-language formula even if there are no
inductive objects. The induction scheme for every full-language formula P
(with any parameters) is:

    Zero(z) and P(z) and
      (forall a,b, N_z(a) and S(a,b) and P(a) -> P(b))
    -> forall a, N_z(a) -> P(a).

This is the precise induction convention previously accepted; the original
informal phrase “induction over naturals” alone does not specify it. No
existential Infinity sentence occurs in the closed axiom family.

First, the derived uniform comprehension principle of Section 2.1 follows
directly from comprehension and the corrected Uniformity schema. It yields an
empty uniform z. Let P(a) mean that a and all of its first members are uniform.
P(z) holds vacuously. For P(a), comprehension of `y=a or m(y,a)` yields a
uniform successor b with P(b). Any other first-membership successor of a is
identical to b by extensionality. Hence the relational induction hypothesis
holds for P. All N_z objects and their members are therefore uniform.
Comprehend N_z using the uniform parameter z: its uniform representative w
exists and has exactly those objects as first members. Zero belongs to w.
For any a in w, P(a) gives a successor b. Every inductive object contains a,
and by its closure contains a successor of a, necessarily b. Thus b belongs
to w. So w is inductive, and by definition it is contained in every inductive
object. We have proved existence of the least inductive w, its uniformity,
and uniformity of all its members. There is no appeal to a pre-existing
inductive object in this argument.

Once w exists, N_z(a) is equivalent to m(a,w). Relational induction then
coincides with the old conditional induction scheme based on a least
inductive object. Conversely the old base theory, with explicit Infinity,
satisfies relational induction because of this equivalence and uniqueness
of zero. The two specifications thus have exactly the same models; ordinary
first-order completeness gives their external deductive equivalence. The
same argument works with TI. In the repository the bridges are
`DESTOriginal.exists_uniform_omega`, `DESTOriginal.original_iff_base`,
`DESTOriginal.original_TI_iff_reference`, and
`DESTOriginalClosed.satisfies_iff_base`.

The rest of the proof may therefore work with the derived least inductive
object, without adding it as an axiom to B.

## 2. The lower bound: B has the arithmetic consequences of Z2

The arguments are valid in any first-order model of B, not just the model
constructed in the verified consistency proof. Use m for first membership,
r for second membership, and U(a) for agreement of the two extensions of a.

### 2.1 Uniform comprehension and finite constructions

For any first-language formula p(y,c) whose parameters c are uniform, if
all its values are uniform, comprehension yields an object a with
r(y,a) iff p(y,c). If a were nonuniform, uniformity would imply p(a,c),
contradicting the assumption on all values. Thus a is uniform, and its
m-extension is precisely p. This is an unrestricted formula schema in m.

In particular, the empty object is uniform. Finite sets of specified uniform
objects are uniform, by comprehension of disjunctions of equalities. For
uniform a,b the Kuratowski pair {{a},{a,b}} exists, is uniform, and has the
usual ordered-pair identity property by extensionality. All these relations
have first-language definitions, even though their existence proof uses
uniformity. If a uniform object g has only uniform members, adjoining a
uniform p to its extension produces a uniform object with only uniform
members, using the formula m(y,g) or y=p. This fact will construct internal
finite function graphs one pair at a time, without Replacement or Power Set.

### 2.2 Internal natural numbers, including in nonstandard models

Let z be empty and w the least inductive object. Write N(a) for m(a,w).
The successor relation S(a,b) says that the extension of b is the extension
of a together with a. It is first-language and functional by extensionality.
The derived least-inductive property gives N(z) and a successor in N for every N(a).

Induction proves the following simultaneously or in separate instances.

* Every number and every member of a number is uniform. The base is empty;
  uniform comprehension constructs the successor and extensionality
  identifies it with any candidate successor. Its members are uniform.
* Every number is transitive: for a successor b of a, a member of a member
  of b is either a member of a directly, or is a member of a member of a.
  In both cases it belongs to b.
* Every number is irreflexive. For a successor b of a, if m(b,b), either
  b=a, giving m(a,a), or m(b,a); in the latter case m(a,b) and transitivity
  of a give m(a,a). Both contradict the induction hypothesis.
* Every member of a number belongs to N: this holds vacuously for zero and
  follows for successors from the induction hypothesis and N(a).
* Every number is zero or the successor of a number: immediate induction.
* Zero belongs to each successor of a number. The successor of zero contains
  zero; the property is preserved on taking successors.

These properties imply the Peano successor axioms. A successor cannot be
empty because it contains its predecessor. If a and b have the same
successor and a != b, then m(a,b) and m(b,a); transitivity and irreflexivity
of a give a contradiction. Thus successor is injective on N.

The collection N is definable in the first language without parameters:
say that an object belongs to a least inductive object based on an empty
object. First extensionality implies uniqueness of the empty object and of
the least inductive object. All values of this formula are uniform, so its
uniform representative must be w. In particular w is uniform. None of
these arguments uses full set induction.

### 2.3 Addition and multiplication by internal finite recursion

We give explicit reasoning because external iteration over standard naturals
would not suffice in a nonstandard model. Let H(a,b,c) be any fixed
first-language relation which, for numbers a,b, has a unique numerical c.
Fix numerical a and initial value i. For a numerical n, a recursion graph
through n means an object g whose m-extension is exactly a function graph
with index domain the members of S(n), numerical range, value i at z, and
H(a,g(k),g(l)) whenever both k,l belong to the domain and S(k,l). This is
first-language definable by quantifying over the Kuratowski pairs in g.
There is no requirement that every candidate graph be uniform.

Induct on n with the full DEST induction schema to prove existence of a
uniform recursion graph having only uniform members. For n=z, use the
singleton graph containing the pair (z,i). If g is a graph through n, write
s=S(n) and choose c with H(a,g(n),c). Adjoin the uniform pair (s,c) to g
by uniform comprehension. Since s is irreflexive, s is not in the old
index domain. The new domain is the old one together with s. The only
new transition ends at s, whose predecessor is n by successor injectivity.
There is no new transition starting at s: S(s) cannot belong to S(s), by
irreflexivity. Thus the resulting graph satisfies the recursion property.
This argument invokes the internal induction instance with a formula
asserting existence of a uniform graph, not an external recursion of length
n. All index and value objects in the construction are uniform.

For uniqueness of the value at n, suppose g and h satisfy the recursion
conditions through n. Apply internal induction to k in N, with the
property that if k belongs to their common domain then their values at k
agree. The base is the specified initial value. If S(k) belongs to their
common domain then k belongs to it by transitivity of the domain (the
successor of n). Functionality of H gives agreement at S(k). Hence their
values at n agree. Uniformity of the candidate graphs is unnecessary.
Extending a graph through n proves the recursion equation for the unique
value at S(n).

Define a+n to be the unique output obtained with initial value a and step
H(a,b,c) iff S(b,c). Then a+z=a and a+S(n)=S(a+n). Define a*n with initial
value z and step H(a,b,c) iff b+a=c. This gives a*z=z and a*S(n)=a*n+a.
These are exactly the standard recursive PA axioms. All the operations are
first-language definable, without free parameters once the unique w and z
are defined. Full induction for their arithmetic formulas follows by
translation into DEST's induction schema. This proves PA on N in every
model of B, including models with nonstandard N.

### 2.4 Parameter-free full second-order comprehension

Take the set sort to consist of **all** objects X such that
forall y (m(y,X) implies N(y)). Do not require uniformity of X: doing so
would put second membership into bound quantifiers. Extensionality gives
extensional equality for this sort. Its elements need not be uniform.

Translate numerical quantifiers by N and set quantifiers by the displayed
subset guard. Translate arithmetic terms by their unique-value relational
formulas from 2.3 and set membership by m. Thus every second-order formula
translates into the first membership language, even with arbitrary
alternations of number and set quantifiers.

Let p(n,k) have no free set variables, but possibly numerical parameters k.
Those parameters, and w if it is used explicitly, are uniform. The formula
N(n) and p*(n,k) has only uniform values. Uniform comprehension therefore
produces a first-extension representative that is a member of the set sort.
This is every parameter-free comprehension instance. In fact numerical
parameters are allowed, so any convention excluding them as well is covered.
Full induction, including formulas with free set parameters, holds by
DEST's induction schema. Induction is not subject to uniformity of its
parameters. The two-sorted structure therefore satisfies parameter-free Z2.

Now if Z2 proves an arithmetic sentence s and a model of B falsified s*,
take a countable such model (first-order completeness and downward
Löwenheim–Skolem). The constructed arithmetic structure is countable and
satisfies parameter-free Z2, with the same number domain as the original
model. Friedman's theorem restricts its set domain, leaving the number
structure unchanged, to produce a model of full Z2 falsifying s. This is
impossible. Completeness gives B |- s*.

## 3. The upper bound: fixed finite fragments in S

Work inside the interpreted powerset-free set theory S from reduction 2.
We use full Separation, Collection, Infinity, Foundation, well-orderability
and every set countable. Constructibility supplies the definable canonical
well-order with set-sized initial segments; any nonempty definable class
therefore has a least element (take one witness and separate on its initial
segment). These facts suffice for the fixed-formula definable recursions
used below. No uniform ambient truth predicate is assumed.

Fix any *external* finite fragment T0 of T. Let P be the finite list of
first-language formulas appearing in its comprehension and uniformity
instances. For a fixed arithmetic sentence s whose preservation is desired,
also include s* and the arithmetic definitions. Make a finite collection
Delta closed under subformulas that includes:

* every formula in P, its existential witness test, and its representation
  test exists a forall y (y in a iff p(y,c));
* the first-extensionality axiom, empty set, successor, and least-inductive
  formulas, and exists y (y in a);
* the chosen s*.

For any set seed A, close A under the least witnesses for existential
subformulas of Delta. For a given closure stage and each fixed existential
formula, Separation on the finite Cartesian power of the stage gives the
parameter tuples for which a witness exists. Collection and Separation yield
the set of their least witnesses. Take the union of this with the stage.
The finite list gives a definable successor-stage operation. Iterate it
along omega by recursion on natural numbers using Collection, then Union.
The resulting set reflects every formula in Delta by structural induction:
atomic formulas are absolute for restricted membership, boolean operations
preserve equivalence, and every ambient existential with parameters in the
hull has a selected witness in the hull. This reasoning is a finite
metatheoretic proof in S for each specified Delta. It does not evaluate
arbitrary internally coded ambient formulas.

Apply the construction to the seed omega union {omega}, obtaining U.
For each p in P and parameter tuple c from U there are two cases.
If the ambient p-class is a set, its unique representative is in U by
reflection of the representation test. If it has no representative,
then outside U and any finite list there is a p-witness: otherwise
Separation on U united with the finite list would represent the class.
Recursively choose an infinite sequence of distinct such witnesses using
the canonical well-order. Collection gathers the sequences for all tuples
and the fixed finite list P. Also choose an infinite sequence outside U
(the universe is not a set, by Separation and Russell's argument). Close
the union of U and the gathered witnesses under the same Delta operations,
obtaining M. Both U and M reflect Delta, and M-U contains infinitely many
objects. The two sets are countable within S.

### 3.1 The finite family of definable extensions

Let e(a)={y in M: y in a}, for a in M. Let D consist of e(a) for a in U,
all singletons {b} for b in M-U, and {y in M: p^M(y,c)} for p in P and c
from M. All these sets exist by Separation on M, because p^M is just the
fixed relativized formula. Collection gathers the families of extensions
into a set D. Countability follows from the axiom of S. No P(M) is needed.

Call B in D protected if it has the last form with its parameters in U.
The following are consequences of reflection:

(a) e is injective by first-extensionality in M.
(b) If e(a)=B is protected, the representation test with a as witness holds
    in M. Reflection of its inner universal formula shows that a is an
    ambient representative. Reflection of the existential representation
    test in U yields an ambient representative in U. By extensionality,
    a belongs to U.
(c) If B is protected but not e(a) for an a in U, its ambient p-class has
    no representative, for otherwise U would contain that representative.
    Hence B contains the infinitely many chosen p-witnesses outside U.
(d) A singleton {b} for b outside U is not protected: if it were, reflection
    of the existential p-witness test would yield a member in U, impossible.
(e) Such a singleton is not e(a) for a in U: reflection of exists y(y in a)
    would yield a member in U. This is separate from (d).

### 3.2 Back-and-forth inside S

Prescribe F(a)=e(a) for a in U. This is injective. On M-U and the remaining
part of D, construct a bijection by alternating through internal enumerations
of both countable sets. At a step covering a new protected extension B,
choose a previously unmatched a in B-U. By (c) infinitely many candidates
are available, and by (b) none has e(a)=B. At a step covering a new
unprotected extension, choose a fresh object outside U avoiding e(a)=B;
by injectivity (a) there is at most one excluded object. At a step covering
a previously unmatched a outside U, choose a fresh singleton of a point
outside U, avoiding e(a). By (d) and (e) it is neither protected nor
prescribed; infinitely many are available. At every stage the finite list
of earlier assignments excludes only finitely many candidates. Enumerations
exist because both sets are countable in S; the choices can be made using
least indices. The union of the finite partial matchings is a set by
Collection and Union, and covers both sides. Join it with the prescribed
part to obtain a bijection F:M -> D. The reasoning is internal, so an
internally finite list may be externally nonstandard in length without
invalidating it.

Define m1(y,a) iff y in a (restricted to M) and m2(y,a) iff y in F(a).
Both extensionalities hold, the second by injectivity of F. Every selected
comprehension instance holds because its extension lies in D. Uniformity
holds precisely on U by the construction. If an instance of uniformity
has uniform parameters and its extension is assigned to an object outside
U, that extension is protected and the assignment placed the object in
its extension. Thus the corrected uniformity implication holds. All
required axioms from P are satisfied simultaneously, with the same M,m1,m2.

### 3.3 Natural numbers, induction, and arithmetic preservation

The seed contains all internally natural numbers of S and omega itself.
First-membership traces on these objects are their ambient members. Their
successor operations and least inductive property agree with the ambient
ones by Delta reflection (the successor is also unique by extensionality).
This supplies the Infinity sentence. For every fixed formula of the full
language on M, with arbitrary parameters, Separation in S gives its truth
set on M by relativizing quantifiers and replacing second membership by
membership in the assigned extension. Full first-membership set induction
holds: if there were a nonempty set of counterexamples, Foundation in S
would supply an m1-minimal counterexample, contrary to progressiveness.
Natural induction holds by the same internal natural-number induction of S,
using the omega and successor agreement. No assertion of *external*
well-foundedness or *external* standardness is used.

The chosen arithmetic sentence s* is first-language. Delta reflection
makes its truth in M equal its truth in the S universe. In S the arithmetic
translation s* uses ordinary von Neumann natural numbers and finite
recursion, hence is equivalent to the original arithmetic sentence s.
In particular, for every fixed T0 and every fixed s, S proves that such
an M exists, satisfies T0, and satisfies s* exactly when s holds.

## 4. The metatheoretic conclusion

Suppose T proves s*. The actual finite proof uses a finite fragment T0.
The construction in section 3 for this T0 and s is a proof in S. Soundness
for that particular proof is provable in S: it is just the finite sequence
of ordinary first-order soundness steps for formulas in a set structure.
Thus S proves s. Reduction 2 interprets S in Z2 and preserves the natural
number structure, so Z2 proves s. Since B is a subtheory of T, section 2
and this implication give exactly the three-way equivalence claimed above.

Taking s to be 0=1 gives the equiconsistency in the ordinary external sense.
Taking s to be the arithmetized consistency statement for Z2 and applying
Godel's second incompleteness theorem shows that, if Z2 is consistent, T
(and hence B) does not prove that consistency statement. We have not proved
that Z2 proves Con(T). The finite-fragment construction is a schema of
proofs for externally fixed lists; treating it as a single internal
reflection theorem would be an invalid strengthening.

## 5. Lean verification boundary

The original ten green source files and all focused omega/SU/Zermelo modules
are retained. This revision adds the independent closed Infinity-free axiom
family, the two-way semantic equivalence to the previous base theory, and an
arithmetic interpretation theorem whose only theory hypothesis is Original.
The arithmetic source includes internal recursion, addition/multiplication,
functional two-sorted syntax, parameter-free comprehension and full induction
for arbitrary models, not only models with standard natural numbers. The
finite-fragment matching and proof-support lemmas are also included.

The precise mathematical conclusion is the equality of arithmetic consequences
in the Claim, and in particular Con(B) iff Con(Z2) iff Con(T), in the ordinary
external metatheoretic sense. The proof uses the published reductions in
Section 1 and ordinary first-order completeness. It is not a claim that Z2
proves Con(B), nor a result about the full second-order semantics of Z2.

`DEST/ExactStrengthSpecification.lean` spells out the two assumed model-level
consequences of the published reductions. `DEST/SetLanguage.lean` through
`DEST/SetFragment.lean` check the construction using internal sets, including
the enumeration graphs, recursion histories, and separation of induction
counterexamples. The proof-transfer theorem reflects first-language
conclusions of the declared DEST calculus into each such weak model.

`DESTExact.consistency_from_z2_model` additionally proves syntactic consistency
of the two DEST calculi from a Z2 model and the constructible interpretation.
The verified equivalence is at the level of Henkin model existence. The
published metatheorems are hypotheses. Completeness for the proof calculi and
the full arithmetic-consequence comparison are supplied by the external
mathematical argument above.
