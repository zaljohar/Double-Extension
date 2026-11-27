# Mathematical construction

## 1. Ambient structure

In ZFC let A = V_{ω₁} with actual membership. Every countable subset S of A is
an element of A, since the supremum of countably many countable ranks (plus one)
is countable. A is extensional and its membership is well-founded. In the Lean
implementation the ambient is mathlib's `ZFSet.{0}` instead: `ZFSet.range` gives
an ambient representative for a countable family. The argument needs only this
representation property, first extensionality and well-foundedness.

## 2. Two countable witness hulls

Start with the countable seed of standard von Neumann numerals and ω. Given a
countable seed and a fixed excluded collection, take the union of countably many
stages. At each stage include witnesses, whenever they exist, for the following
countable family of tests over finite parameter lists from that stage:

- A counterexample to any first-language formula (the Tarski–Vaught witness).
- An ambient set representing the extension of a first-language formula.
- A witness that an ambient set and a formula's ambient extension differ.
- A point in a definable extension outside the excluded collection and outside
  a given finite list of forbidden objects.

The tests are countably indexed, so all stages and the final hull are countable.
Each finite list of hull parameters occurs at a finite stage, so every successful
test has a hull witness. The counterexample property proves elementary agreement
with the ambient by structural induction on formulas.

First construct U from the seed (excluded collection empty). Construct M from U,
with U as excluded collection. Thus U ⊆ M, both countable, both elementary for
first-language formulas. The extra tests explicitly witness the properties used
below; no general Löwenheim–Skolem theorem is assumed.

## 3. Protected and fixed extensions

Let E(a) = {y ∈ M : y ∈ a}. Let D be all subsets of M definable by first-language
formulas with parameters from M. D is countable. Extensionality of E on M follows
from the difference-witness test: agreement of two extensions on M implies
ambient agreement, then ambient extensionality.

Call S ∈ D protected if it has a definition using only parameters in U.
Call S fixed if S = E(a) for a ∈ U. Fixed implies protected. Conversely, if S is
protected and S = E(a) for some a ∈ M, the difference-witness test ensures that a
represents the formula's ambient extension. The representation-witness test in
U finds the unique ambient representative in U. Thus a ∈ U, and S is fixed.

If S is protected but not fixed, its ambient defining extension cannot have a
representative, and therefore cannot be countable. It cannot be contained in U
plus any finite list. The outside-witness test in M therefore ensures that S has
points in M \ U outside any prescribed finite list. The same argument applied
to the universal formula shows M \ U itself has infinitely many points; no
ambient set contains every ambient object because membership is well-founded.

A singleton {b} for b ∈ M \ U is definable but cannot be protected: a defining
formula with U-parameters would have a witness in U, by elementarity, making its
unique member belong to U. In particular these singletons are free (not fixed).

## 4. Matching

On the left take M \ U; on the right take the definable nonfixed extensions.
Allow a match a ↔ S exactly when E(a) ≠ S, and additionally require a ∈ S if S is
protected. Both sides are countable. Every vertex has an allowed neighbor outside
any finite list of forbidden neighbors:

- For an outside object a, use a singleton of an outside object, avoiding the
  finitely many previously used extensions and E(a). Such singletons are free
  and not protected.
- For a protected free extension S, choose an unused outside member of S. Its
  first extension cannot equal S, since otherwise it would belong to U.
- For a nonprotected free extension S, choose any unused outside object except
  the at most one object a with E(a)=S.

Enumerate both sides. Alternately extend a finite injective matching to cover the
next left and next right vertex, preserving all previous pairs. Their union is a
bijection e and every matched pair satisfies the allowed relation.

## 5. Model

Assign F(a)=E(a) for a ∈ U and F(a)=e(a) for a ∈ M \ U. The first images are
exactly the fixed extensions, the second exactly the free ones. Hence F is a
bijection M → D. By construction F(a)=E(a) iff a ∈ U. Interpret second membership
by y ∈₂ a iff y ∈ F(a). Interpret first membership by ambient membership on M.

First extensionality follows from injectivity of E, second from injectivity of F.
Every first-language formula with parameters has an extension S ∈ D, which has a
preimage under F: comprehension. An object is uniform iff a ∈ U. If a defines a
protected extension but is outside U, the allowed relation forces a ∈ F(a), i.e.
a ∈₂ a. This proves the corrected Uniformity axiom by contraposition. Crucially,
there is no restriction on the parameters in comprehension itself.

## 6. Induction and consistency

The original membership on M is externally well-founded. Thus set induction
holds for every predicate on M, even one defined using both memberships. This
implies ordinary transfinite induction along first-membership ordinals. All
standard von Neumann numerals and their ambient ω were included in U at the seed.
The ω object's first-extension members are exactly those numerals; successor
and zero have their usual membership descriptions. It is the least inductive
set, and ordinary external induction proves natural-number induction for every
predicate on M.

The entire mathematical construction uses only ZFC. Consequently ZFC proves
existence of a set-sized model of corrected DEST with first-membership induction,
and by the soundness theorem gives the indicated relative consistency. The Lean
formalization implements the model-existence argument, not a separate encoding
of the ZFC metatheory and its consistency predicate.
