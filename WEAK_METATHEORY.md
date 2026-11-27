# Obligation 3 — finite DEST fragments in powerset-free set theory

## Result and scope

Let B be corrected original DEST, with the relational natural-number induction
scheme of `DEST/OriginalClosedSpecification.lean`, but no Infinity axiom.
Let T = B + TI1. No Subset Uniformity axiom is used in this result.

**Fixed-fragment theorem.** For every externally fixed finite fragment T0 of T
and every externally fixed first-language formula p, the powerset-free
constructible metatheory S proves that there is a countable set structure
(M, m1, m2) satisfying T0, containing its own natural-number objects, and
reflecting p with parameters in M. Here m1 is ambient membership restricted to
M. In particular, for a fixed first-order arithmetic sentence sigma and its
first-language set-theoretic translation sigma*, the construction preserves
truth of sigma.

The result is schematic in the externally fixed formulas. It does NOT claim
that S has a truth predicate for its universe or proves the single sentence
Con(T). The proof below discharges the weak-metatheoretic mathematical
obligation using Separation, Collection, elementary set operations, Infinity,
Foundation and a definable least-witness operation. It does not require Power
Set, Hartogs, a set of all reals, a rank hierarchy, or a set containing all
countable sets.

The independent published interpretation used here is Kanovei–Lyubetsky,
*Notes on the equiconsistency of ZFC without the Power Set axiom and second
order PA*, Theorems 5.2, 1.2 and 8.6, and Lemma 7.3, arXiv:2507.11643v4
(https://arxiv.org/html/2507.11643v4; published Axioms 14 (2025), 865,
https://doi.org/10.3390/axioms14120865). Their constructible cut L* satisfies
ZFC minus Power Set with Collection, and has the canonical definable
well-order of its constructible sets. The cut, not necessarily the entire L,
is used. The well-order admits least elements of nonempty definable classes:
choose a witness, then restrict to its bounded initial segment (contained in a
constructible level) and apply Separation and the well-order property. This is
the only global-choice property needed below. Their tree interpretation and
transitive cut preserve the number structure. Our proof uses only countability
of the explicitly constructed carriers; it does not require every set of S to
be internally countable.

## 1. Set operations available in S

Throughout the following argument work inside S. All occurrences of a fixed
formula refer to that actual first-order formula, with its quantifiers ranging
over the S universe. The construction is performed for each fixed finite
list of formulas separately.

1. A total, first-order definable function G on a set A has a set range and a
   set graph by Collection and Separation. Indeed collect a set C of possible
   values, form A x C, separate the graph and take its image. Binary products
   do not require Power Set: for each a use Pairing and Collection on B to
   collect all ordered pairs (a,b), then Collection on A and Union. Any
   extraneous elements are removed by Separation. Equivalently use the
   Replacement consequence of Collection and Separation directly for the
   pair map and the graph map.
2. The natural-number recursion theorem for a total, first-order definable,
   functional step G follows without Power Set. Define a finite history to be
   a function on n+1 with the given seed and the required successor rule.
   Induction proves existence by appending one ordered pair and proves
   uniqueness by agreement on initial segments. Apply Collection to n in
   omega to gather the unique histories. Separate the actual histories and
   take their union. This gives the entire function on omega. All the
   formulas involved are fixed, with G's definition inserted. This argument
   also works with several simultaneous state variables coded by tuples.
3. For a given set d, the set d^{<omega} of finite lists exists: the set of
   lists of length zero is the singleton empty list, and the next length
   is obtained by the image of the Cartesian product of the previous
   length with d under appending. Use (2) and Union. This does not use the
   set of all subsets of omega x d.
4. If d is nonempty and has an enumeration e:omega -> d, then finite lists
   from d have an enumeration: use the usual numerical codes for finite
   lists of natural numbers, decode and apply e entry by entry. Finite
   products of such enumerated sets, including a nonempty finite index set,
   are enumerated by standard numerical pairing. Images of these sets are
   enumerated by composition. A union of a finite number of nonempty
   enumerated sets is enumerated by interleaving. Empty components may be
   omitted or padded with an existing element of the nonempty union.
5. If (d_n,e_n) is a definable sequence of sets and enumerations, its union
   has an enumeration by mapping a numerical pair (n,k) to e_n(k). For a
   subset of a countably enumerated set, a least preimage in omega yields
   an injection into omega; if nonempty it admits an enumeration by
   restricting to indices hitting it and using a fixed member as default.

Thus all set and enumeration recursions below can be performed by (1)–(5).
There is no use of a principle saying that an arbitrary external countable
collection of S-objects is an S-set.

## 2. Finite witness operations

Let P contain the finitely many formulas defining the comprehension and
Uniformity instances in T0. Add the finite list of formulas whose truth must
be reflected, including sigma* if needed. In the Lean implementation a
formula with free variables is evaluated with a finite list of values in
de Bruijn order. This coding is equivalent to ordinary first-order
relativization by `DESTSemantic.first_language_translation`.

For each fixed formula in P, include one witness operation for each of its
universally quantified subformulas forall x psi(x,c): select the least
counterexample x to psi(x,c) if there is one. Include these additional
witness operations for every fixed unary defining formula p(x,c):

- **rep:** an a such that forall x (x in a iff p(x,c));
- **diff:** for a given a, a counterexample to that equivalence;
- **exists:** an x satisfying p(x,c);
- **outside:** an x satisfying p(x,c) and lying outside a given set u and
  outside a supplied finite banned list l.

Also include a disagreement witness for distinct sets a,b (using
p(x,b) = x in b), an existential witness to membership in a, and an outside
witness for the universally true formula. These correspond to the additional
three queries in `DESTWeak.queries`.

Every operation is totalized by returning the empty set when no witness
exists. When a witness exists, choose the least one in the definable
constructible well-order. For this fixed finite family, dispatch on the
query number by a finite disjunction of its explicitly written formulas.
There is no evaluation of an arbitrary variable formula code in the proper
class universe, nor a truth predicate there. The finite query list can be
unrolled when writing the S proof. List lookup and tuple handling are
ordinary first-order definable operations; if out-of-range arguments are
allowed, use the same false-atom convention as the Lean syntax.

## 3. Two actual set-coded hulls

Fix the finite query family Q. For a set u to be avoided, and a nonempty
countable set d, put

    Next_u(d) = d union {pick(q,u,l,b): q in Q, l,b in d^{<omega}}.

The domain Q x d^{<omega} x d^{<omega} is a set by Section 1. The total
selector is a fixed first-order definable function, so its range is a set
by Collection and Separation. The union with d exists. Moreover, an
explicit enumeration of d gives an explicit enumeration of Next_u(d) by
Section 1. If a query family is empty, the next set is simply d.

Starting from a countably enumerated nonempty seed d0, form

d_{n+1} = Next_u(d_n), H_Q(u,d0) = union_{n in omega} d_n.

Apply the recursion proof of Section 1 to the pair (stage, enumeration).
Each stage, the entire sequence of stages, and its union are sets of S.
The hull has an enumeration obtained by numerical pairing. Since the
stages increase, every internally finite parameter list in the hull lies
in a single stage: take the maximum of the finitely many least entry
stages. The same is true of a finite banned list. Hence every successful
query using those parameters has a witness in the hull itself.

Define

    seed = omega union {omega},
    U = H_Q(empty, seed),
    M = H_Q(U, U).

Both are actual sets, both are countable in S, and U is a subset of M.
Both contain every ambient finite ordinal and omega. The second hull's
outside tests avoid the **actual set U**, not an arbitrary proper class.

By induction on the externally fixed syntax of each formula in P, both
U and M agree with the ambient universe on its truth with parameters
in the respective hull. Atomic equality and membership agree by restriction;
implication is immediate; for a universal quantifier, any ambient
counterexample can be chosen in the hull by the corresponding query, and
the subformula is reflected there. This is finite-formula Tarski–Vaught,
not full elementarity. The proof in Lean is `DESTWeak.reflect`.

## 4. Discharging every finite matching condition

Let E(a) = {x in M : x in a} for a in M. By Separation, E(a) is a set.
Let D be the union of these three set families:

    {E(a): a in U};
    {{b}: b in M-U};
    {{x in M: p^M(x,c)}: p in the fixed list P, c a parameter tuple from M}.

It is harmless to include all lists of parameters in the final family;
fixed-length tuples suffice for the actual axioms. For fixed p, each
extension is obtained by Separation on M using the fixed relativized
formula, then Collection takes its range over M's parameter lists.
Finite union gathers the families. The explicit enumerations of M and its
finite lists give countability of D. No P(M) is formed. Call B protected
if it is the extension of a requested defining formula with parameters
from U.

(a) **Injective traces.** If a,b in M are distinct, their ambient extensions
differ by Extensionality. The disagreement query supplies a point in M
where they differ. Thus E(a) != E(b).

(b) **Protected traces must be fixed.** If E(a)=B for a protected B defined
by p with U-parameters, an ambient disagreement would have a witness in M.
Finite reflection of p then contradicts the trace equality. Therefore a
is an ambient representative of p. The rep query in U gives a representative
b in U. Extensionality yields a=b. Conversely if p has any ambient
representative, the rep query in U supplies it and its trace is B. These
observations prove the representative condition and its contrapositive.

(c) **Fresh outside witnesses.** If a protected extension B is not E(a) for
any a in U, its defining ambient p-class has no set representative by (b).
Let l be any internally finite list from M. Were every p-witness contained
in U union range(l), Separation on that actual set would produce the missing
ambient representative. Hence a p-witness exists outside U and outside l.
The outside query in M supplies one in M, and finite reflection gives that
it belongs to B. This proves the fresh-supply condition for every internally
finite banned list. No assertion about cardinality of a proper class is
needed. Likewise the true formula has no ambient set representative
(a universal set contradicts Foundation, or Russell Separation), giving
an unlimited supply outside U independent of B.

(d) **Outside singletons are unprotected.** If {b} for b in M-U were
protected, the exists query with U-parameters would supply a witness in U;
its trace membership would force that witness to be b. Contradiction.

(e) **Outside singletons are not fixed.** If {b}=E(a) for a in U, the
membership witness query in U supplies a member of a in U. Its membership
in E(a) again forces it to be b. Contradiction.

These are all the fields of `DESTStrength.HullData`. The inclusion and
countability fields follow from the definition of D. The Lean theorem
`DESTWeak.hull_data` supplies them all, not as new hypotheses.

## 5. Matching uses only set operations in S

Prescribe F(a)=E(a) for a in U. These assignments are injective. Write
O=M-U and J=D-{E(a): a in U}; both are countably enumerated sets by
Section 1. Every b in O supplies the singleton {b} in J. A match between
a in O and B in J is allowed if E(a)!=B and, when B is protected, a in B.

Construct finite partial injective matchings, alternately covering the
next element of O and the next element of J in their enumerations. If
already covered, leave the matching unchanged. For an unmatched a, choose
a new singleton of a point in O, avoiding E(a). Infinitely many candidates
are available by (c); (d) and (e) guarantee eligibility. For an unmatched
B, if protected choose a fresh point by (c); it cannot have trace B by
(b). If unprotected choose any fresh outside point except the at most one
whose trace is B, using (a) and (c). In each case choose the least eligible
index in the appropriate enumeration. Finite matching lists and their
finite extensions are sets, and the rule is a fixed definable functional
step. Thus the entire sequence exists by Section 1. Its union, joined to
the prescribed part, is an injective surjection F:M -> D. There is no
use of a set of all possible partial matchings or of arbitrary choices.

Define m1(x,a) iff x in a, restricted to M; define m2(x,a) iff x in F(a).
Both relations are subsets of the set M x M, formed by Separation. Both
Extensionality axioms hold; the first by (a), the second by injectivity of F.
Every requested comprehension extension has a representative by
surjectivity. Exactly U is uniform, by the fixed and allowed assignments.
If a requested Uniformity instance has uniform parameters and extension B,
then B is protected. Its representative outside U would have to belong to
B, so the corrected Uniformity implication holds.

## 6. Induction and arithmetic preservation

Because the seed contains omega and all its elements, traces of finite
ordinals and their successors are the actual ones. The first trace of
omega is all the ambient natural numbers. It is inductive, and least:
for any internally inductive a in M, ordinary ambient induction proves
that a's trace contains every natural number, using trace extensionality
to identify its successor witnesses. It follows that the formula
"belongs to every inductive object" defines exactly the members of omega.
Thus the Infinity-free relational induction convention is satisfied.
For each fixed full-language induction formula, its relativization to the
set M, with second membership replaced by the formula for F, is a formula
of S. Apply ambient natural-number induction to that formula. For each
fixed set induction formula, separate the set of counterexamples inside M;
Foundation in S supplies a membership-minimal one if it is nonempty. This
contradicts progressiveness. This verifies all desired induction instances,
including those mentioning both memberships. It uses only *internal*
Foundation and natural-number induction, not external well-foundedness or
standardness of an arbitrary model of S.

Finally include the fixed first-language translation sigma* of an
arithmetic sentence sigma among P. Arithmetic is defined by ordinary
von Neumann naturals and finite addition/multiplication recursions in S,
which exist by Section 1. The relativization of sigma* to M agrees with its
ambient interpretation by Section 3. Hence the construction preserves truth
of sigma, in the precise sense required for each fixed sigma. The Lean
`DESTSet.finite_fragment_inside` endpoint includes this reflection property,
and `DESTSet.first_sentence_of_internal_model` composes it with finite proof
support and soundness in the declared calculus.

## 7. The conclusion and verification boundary

This completes the fixed-fragment mathematical construction in S. In fact,
only finite witnesses, definable Collection and Separation, countable
recursion and finite list codings have been used. There is no Power Set
operation, no all-formulas truth predicate in a proper class, and no
assumption that an arbitrary externally countable subset belongs to S.

For any actual proof of an arithmetic sentence sigma* in T, choose its
finite axiom support and apply the preceding theorem in S. Ordinary
first-order soundness for this fixed proof gives S |- sigma. The published
arithmetic-preserving interpretation of S in Z2 gives Z2 |- sigma. The
other direction is the parameter-free comprehension interpretation and
Friedman's arithmetic-preserving reduction already stated in
EXACT_STRENGTH_ARGUMENT.md. With those published reductions, the conclusion
is equality of arithmetic consequences and hence external equiconsistency
of B, T, and Z2. It is not an assertion Z2 |- Con(T).

**Lean verification.** The arbitrary-model proof sits in `DEST/SetLanguage.lean`
through `DEST/SetFragment.lean`. It takes finite reflection from the published
constructible-cut result. The two witness-closed domains are internal sets,
and the model's own enumeration graphs and finite histories drive the
matching. Definability of second membership makes the two induction arguments
applicable even when the weak model's natural numbers are nonstandard.
Separation in a larger bounded domain collects the graph of second membership
as a set of the weak model.
`DEST/SetCompactness.lean` assembles the fragments in the external metatheory.
`DEST/ExactStrength.lean` uses the two published reductions as hypotheses.
The proof verifies satisfaction in arbitrary models of the stated resources.
An encoding of S-provability and the stronger arithmetic comparison remain
part of the external mathematical argument.
