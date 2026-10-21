/-ai
The digit map from bits to natural numbers is injective.

Cases on both bits reduce an equality of images by the definition of the map.

The embedding of a binary string sends a cons cell to the cons of the image of the head with the image of the tail.

The equation is definitional.

The embedding preserves and reflects the prefix order. The image of one binary string is a prefix of the image of another if and only if the first string is a prefix of the second.

Induction on the first string. The empty string simplifies. For a cons cell, an empty target simplifies by the cons equation of the embedding. A cons target rewrites both prefix relations by the cons criterion and both images by the cons equation, then uses injectivity of the digit map and the inductive hypothesis.

Cone inclusion in Scott's binary system matches neighbourhood inclusion in the LUCID system along this embedding. The cone of one binary string is contained in the cone of another if and only if the neighbourhood of the embedded address is contained in the neighbourhood of the other embedded address.

Rewrite by the cone criterion, the neighbourhood criterion, and the prefix equivalence for the embedding.

The order of finite elements of the binary system matches the order of the corresponding finite elements of the LUCID system. One finite element lies below another if and only if the element of the finite sequence given by the first embedded address lies below the element of the second.

Those elements are the principal filters of the neighbourhoods of the embedded addresses. Rewrite by the order criterion for the finite elements, the order criterion for principal filters, the neighbourhood criterion, and the prefix equivalence.

If a function on the natural numbers is primitive recursive, so is the map sending an argument to the negation code of its value.

The map selects two when the equality characteristic with one is set, and otherwise selects one when the equality characteristic with two is set, and otherwise selects zero. Extensionality is the case split on equality with one and with two. Each equality makes the corresponding characteristic one by the zero test in its definition, and each failure makes it zero, so the selections match the definition of the negation code.

Negation of the neighbourhood enumerated by an index is the neighbourhood enumerated by the negation code of the minimum of that index and two.

Rewrite the enumeration to canonical form. The minimum is at most two, and each of its three values simplifies by the enumeration, the negation code, and the three clauses of negation.

Pointwise negation on the three-point truth domain is a computable map of its presentation to itself.

The map that replaces the first component of a packed pair by the negation code of its minimum with two is primitive recursive, and inclusion of enumerated neighbourhoods along that map is recursively decidable by the inclusion decider of the presentation. The neighbourhood relation of negation is that inclusion, because negation of an enumerated neighbourhood is the enumerated negation code and every enumerated set is a neighbourhood. A decidable relation is recursively enumerable.

If two functions on the natural numbers are primitive recursive, so is the map sending an argument to the conjunction code of their values.

The map selects the second value when the equality characteristic of the first value with one is set, selects two when the characteristic with two is set, and selects zero otherwise. The same case split makes each characteristic one or zero by the zero test, and the selections match the definition of the conjunction code.

Conjunction of the neighbourhoods enumerated by two indices is the neighbourhood enumerated by the conjunction code of the two minima with two.

Both enumerations rewrite to canonical form. Both minima are at most two, and each combination of their values simplifies by the enumeration, the conjunction code, and the three clauses of conjunction.

Pointwise conjunction is a computable map from the product presentation of the three-point domain to its presentation.

The map sending a packed word to the conjunction code of the two minima with two of the components of the first half, paired with the second half, is primitive recursive, and inclusion of the resulting enumerated neighbourhood is recursively decidable. The relation of conjunction on a product neighbourhood is the relation of the underlying binary map after the two preimages of the product, which are the two factors, once the product of two neighbourhoods is known to be a product neighbourhood. That relation is inclusion of the conjunction, rewritten by the enumeration equation, together with the three memberships. Packing through the product presentation makes the relation decidable, hence recursively enumerable.

Postcomposition preserves computability. A computable map between presented neighbourhood systems induces a computable map from the function space of the LUCID system into the first to the function space into the second, relative to presentations built from characteristic bundles.

Evaluation against the first bundle is computable. Composing with the given map stays computable, and currying that composite against the second bundle stays computable.

A computable map out of a product induces a computable pointwise map on a product of function spaces over the LUCID system.

The projections from the product of that product of function spaces with the LUCID system are computable, and composing the product projection with the two function-space projections gives the two pointwise projections. Evaluation of each, paired with the projection onto the LUCID system, is computable. Pairing those evaluations, composing with the binary map, and currying yields the pointwise map.

LUCID negation lifts to a computable endomap of the function space from the LUCID system to the three-point domain.

Apply the postcomposition theorem to the characteristic bundle of that function space and the computability of negation.

LUCID conjunction lifts to a computable map from the product of that function space with itself into the function space.

Apply the pointwise theorem to three copies of the bundle and the computability of conjunction.

The De Morgan combination that negates the conjunction of the two negated arguments is a computable map of that same product type. It is the witness that programs built from the lifted combinators remain computable.

Pair the composites of the two projections with the lifted negation, then compose the lifted conjunction with the lifted negation. Both steps are the closure of computability under pairing and composition.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LenumSubsetChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.HasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.buildData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toStream
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.gammaEquivElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.embStr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.TinterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.TeqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tpres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andMap2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.postcompose
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwFst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwSnd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwArg
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pointwiseBin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LTdata
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LTpres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_length
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_take
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_prefix_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_prefix_of_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_finPrefix_antitone
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.principal_hasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement_not_hasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_eq_of_streamElement_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement_injective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement_injective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_cons_prefix_of_prefix_of_length_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_extend_of_not_hasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.buildData_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.buildData_eq_finPrefix
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd_finPrefix_toStream
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.exists_finPrefix_subset_of_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement_surjective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement_bijective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_false
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_true
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.embStr_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_two
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_eq_canon
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_ne_empty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.master_ne_zero_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.master_ne_one_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.zero_ne_one_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_injOn
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.zero_inter_one_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.one_inter_zero_T
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_inter_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_interEq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_interEq_iff'
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.primrec_TeqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.primrec_TinterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tpres_interEq_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_inter_eq_TinterCode'
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_inter_eq_TinterCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tpres_cons_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tpres_cons_computable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.eq_master_of_master_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.subset_iff_eq_or_eq_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notFn_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.notFn_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.andFn_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwFst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwSnd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwArg

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.curry_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.evalMap_isComputable
@[expose] public section

/-!
# Exercise 7.24 (Scott 1981, PRG-19, §7) — the LUCID system `L`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.24.** (Suggested by the LUCID language of Ashcroft and Wadge: *SIAM Jour. Comp.*
> vol. 5 (1976).) Define a set `Γ` by
>
> `Γ = ⋃ᵢ ({i} × Γ) ∪ {*}`.
>
> Define a system `L = {Γ} ∪ {{i} × X ∣ i ∈ ℕ and X ∈ L}`. Show that `L` is effectively given.
> Show that the elements of `|L|` can be identified with the finite and infinite sequences of
> natural numbers. What is the connection between `B` and `L`? Show that the combinators of LUCID
> can be construed as computable mappings of type `(L→T) → (L→T)` or of type
> `(L→T) × (L→T) → (L→T)`. Conclude that programs in LUCID define computable maps.

## What this file proves

Scott's `Γ` satisfies a *coinductive* set equation `Γ ≅ 1 + (ℕ × Γ)`: an element is either the
basepoint `*` or a pair `(i, γ)` with `γ ∈ Γ` again. Taking the **final** (as opposed to initial)
solution — so that the recursion may run forever — identifies `Γ` with the finite-or-infinite
sequences of naturals directly:

* **`Gamma := List ℕ ⊕ (ℕ → ℕ)`** — a finite sequence (`inl`, terminating at `*`) or an infinite
  one (`inr`, a stream that never reaches `*`). **`star`**/**`cons`** realize `*`/`(i, γ)`;
  **`Gamma_cases`** is the defining equation read as a theorem (every `γ` is `star` or a unique
  `cons i γ'`), and **`cons_injective`** is the "unique" half.
* **`consSet i X = {i} × X`** and **`nbhd l`** (`nbhd [] = Γ`, `nbhd (i :: l) = {i} × nbhd l`) —
  exactly Scott's neighbourhoods, indexed by the finite list of naturals `l` that names them
  (mirroring `ExampleB.cone`/`Example62.embBit`, generalized from `Bool` to `ℕ`-ary branching).
  **`nbhd_subset_iff`** (`nbhd l ⊆ nbhd l' ↔ l' <+: l`) is the master reduction, giving
  **`Lmem`**'s nested-or-disjointness (`L_nestedOrDisjoint`) and hence the system **`L`**.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-! ## `Γ`: finite and infinite sequences of naturals -/


/-! ## The neighbourhood system `L` -/


/-! ## `L` is effectively given -/


/-! ### The primitive-recursive intersection function

Whenever `Lenum n, Lenum m` are consistent (one is nested inside the other), their intersection
is simply the more specific of the two: `Lenum n` if `Lenum n ⊆ Lenum m` (i.e. `isPrefixChar m n =
1`), else `Lenum m`. `selectFn` (from `Recursive.lean`) packages this `{0,1}`-driven choice as a
primitive-recursive arithmetic combinator. -/


/-! ### `L` is effectively given -/


/-! ## Exercise 7.24, second claim — `|L|` is the finite-or-infinite sequences

`toElement : Gamma → L.Element` sends a finite list `l` to the *principal* filter `↑(nbhd l)`
(Scott's finite elements), and an infinite stream `f` to the *limit* filter of its finite
prefixes (`streamElement`, an instance of Scott's `limitFamily`, Definition 1.6's prose).
`toElement_bijective` shows this identification is exact: injectivity is choice-free (finite vs.
finite is `nbhd_injective`; finite vs. infinite is separated by `HasMin`, "having a smallest
neighbourhood", which the finite elements have and the infinite ones provably don't;
infinite vs. infinite recovers `f` pointwise from its prefixes). Surjectivity genuinely needs
choice (build the infinite witness sequence one coordinate at a time; flagged below), matching
Scott's "**can be identified with**" (an existence claim, not a computable retraction). -/


/-! ### Surjectivity (uses choice to build the witness stream, coordinate by coordinate) -/


/-! ## Exercise 7.24, third claim — the connection between `B` and `L`

Scott's binary system `B` (`ExampleB.lean`) branches over `Bool = {0,1}` at each node
(`Σ* = ⋃_b {b} × Σ* ∪ {Λ}`); `L` branches over all of `ℕ` (`Γ = ⋃ᵢ {i} × Γ ∪ {*}`). **`L` is `B`
generalized from `2`-ary to `ℕ`-ary branching** — concretely, digit-wise embedding the bits `0, 1`
as the naturals `0, 1` identifies `B` with the sub-system of `L` consisting of addresses built from
only the two digits `{0, 1}`. `embStr_prefix_iff`/`cone_subset_cone_iff_nbhd_embStr` make this
precise: the embedding `embStr : Σ* → List ℕ` is an order-embedding of the *prefix* posets, hence
(via `nbhd_subset_iff`/`cone_subset_cone`) of the neighbourhood-inclusion posets, hence (via
`principal_le_iff`) of `|B|`'s finite elements into `|L|`'s (`sigmaBot_le_iff_toElement_inl_embStr`).
The same digit-wise embedding on infinite streams (`ℕ → Bool ↪ ℕ → ℕ`) identifies Scott's *infinite*
binary sequences with the `ℕ → ℕ`-branch of `Γ` whose values happen to lie in `{0, 1}`, by the same
argument as `toElement`'s `Sum.inr` case — `B`'s domain `|B|` sits inside `|L|` as the sub-domain of
"binary-valued" LUCID sequences. -/


theorem bitToNat_injective : Function.Injective bitToNat := by
  intro a b h; cases a <;> cases b <;> simp_all [bitToNat]


theorem embStr_cons (b : Bool) (s : ExampleB.Str) : embStr (b :: s) = bitToNat b :: embStr s := rfl

/-- **`embStr` is an order-embedding of the prefix posets** (`Σ*`'s into `List ℕ`'s): it respects
and reflects the initial-segment relation, since `bitToNat` is injective. -/
theorem embStr_prefix_iff : ∀ σ τ : ExampleB.Str, embStr σ <+: embStr τ ↔ σ <+: τ := by
  intro σ
  induction σ with
  | nil => intro τ; simp
  | cons b s ih =>
    intro τ
    cases τ with
    | nil => simp [embStr_cons]
    | cons c t =>
      rw [embStr_cons, embStr_cons, List.cons_prefix_cons, List.cons_prefix_cons,
        bitToNat_injective.eq_iff, ih t]

/-- **The connection between `B` and `L` (Exercise 7.24, third claim), at the neighbourhood
level.** `B`'s cone-inclusion order embeds into `L`'s nbhd-inclusion order via `embStr`: `σ`'s cone
sits inside `τ`'s cone in `B` iff `embStr σ`'s neighbourhood sits inside `embStr τ`'s in `L`. -/
theorem cone_subset_cone_iff_nbhd_embStr (σ τ : ExampleB.Str) :
    ExampleB.cone σ ⊆ ExampleB.cone τ ↔ nbhd (embStr σ) ⊆ nbhd (embStr τ) := by
  rw [ExampleB.cone_subset_cone, nbhd_subset_iff, embStr_prefix_iff]

/-- **The connection between `B` and `L`, at the level of finite elements.** `σ⊥ ⊑ τ⊥` in `|B|`
iff the corresponding `L`-elements (`toElement` applied to the embedded addresses) are `⊑`-related
in `|L|` — `B`'s finite elements embed order-isomorphically into `L`'s. -/
theorem sigmaBot_le_iff_toElement_inl_embStr (σ τ : ExampleB.Str) :
    ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      toElement (Sum.inl (embStr σ)) ≤ toElement (Sum.inl (embStr τ)) := by
  show ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      L.principal (L_mem.mpr (mem_nbhd (embStr σ))) ≤
        L.principal (L_mem.mpr (mem_nbhd (embStr τ)))
  rw [ExampleB.sigmaBot_le_iff, L.principal_le_iff, nbhd_subset_iff, embStr_prefix_iff]

/-! ## Exercise 7.24, fourth claim — LUCID combinators as computable maps

> Show that the combinators of LUCID can be construed as computable mappings of type
> `(L→T) → (L→T)` or of type `(L→T) × (L→T) → (L→T)`. Conclude that programs in LUCID define
> computable maps.

`T` is Example 1.2's three-point truth-value domain (`Example23.T`). We give it a computable
presentation `Tpres` (three neighbourhoods, enumerated by hand — the tiniest instance of Definition
7.1), then show two representative LUCID-style combinators are computable: pointwise **negation**
`notT : T → T` and pointwise **conjunction** `andT : T × T → T`. The general engine is the pair of
*lifting* theorems `postcompose`/`pointwiseBin`: any computable `h : V₁ → V₂` lifts to a computable
map `(L→V₁) → (L→V₂)` via `curry (h ∘ eval)` (Scott's `postcompose`), and any computable
`h : V₀ × V₁ → V₂` lifts to a computable `(L→V₀) × (L→V₁) → (L→V₂)` by evaluating both factors at
the same argument and applying `h`. Since `comp_isComputable`/`paired_isComputable` close
computability under composition and pairing (Proposition 7.3, Theorem 7.4), **every** LUCID program
built from such combinators — however deeply composed — again defines a computable map. This is the
choice-free core of the claim; assembling one concrete presentation of `(L → T)` to state it against
uses `Classical.choice` exactly once (to extract concrete characteristic functions from the existential
deciders of `Lpres`/`Tpres`), matching the classical bridge already used for `toElement_surjective`.
-/

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

/-! ### A computable presentation of `T` (Example 1.2's three-point domain) -/


/-! ### `notT` — pointwise negation on `T`, as a computable map -/


theorem primrec_notCode {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (fun n => notCode (f n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) (Nat.Primrec.const 2)
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 1)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold notCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [ite_eq_left h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [ite_eq_right h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [ite_eq_left h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [ite_eq_right h2, h2', selectFn_zero]

theorem notFn_Tenum (n : ℕ) : notFn (Tenum n) = Tenum (notCode (min n 2)) := by
  rw [Tenum_eq_canon n]
  have hc2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  interval_cases (min n 2) <;> simp [Tenum, notCode, notFn_master, notFn_zero, notFn_one]

/-- **`notT` is a computable map** (relative to `Tpres` on both sides): its neighbourhood relation
`notFn (Xₙ) ⊆ Xₘ` reduces, via `notFn_Tenum`, to the *decidable* `Tpres`-inclusion relation
`X_{notCode (min n 2)} ⊆ Xₘ`, hence is recursively decidable — a fortiori r.e. -/
theorem notT_isComputable : IsComputableMap Tpres Tpres notT := by
  have hcomp : Nat.Primrec (fun t : ℕ => Nat.pair (notCode (min t.unpair.1 2)) t.unpair.2) :=
    (primrec_notCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))).pair Nat.Primrec.right
  have hdec : RecDecidable₂ (fun n m => Tenum (notCode (min n 2)) ⊆ Tenum m) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m, notT.rel (Tenum n) (Tenum m) ↔ Tenum (notCode (min n 2)) ⊆ Tenum m := by
    intro n m
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ notFn (Tenum n) ⊆ Tenum m) ↔ _
    rw [notFn_Tenum]
    exact ⟨fun h => h.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, h⟩⟩
  have key : RecDecidable₂ (fun n m => notT.rel (Tenum n) (Tenum m)) :=
    RecDecidable.of_iff (fun t => hiff t.unpair.1 t.unpair.2) hdec
  exact key.re

/-! ### `andT` — pointwise (sequential/left-strict) conjunction on `T`, as a computable map -/


theorem primrec_andCode {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => andCode (f n) (g n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) hg
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 2)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold andCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [ite_eq_left h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [ite_eq_right h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [ite_eq_left h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [ite_eq_right h2, h2', selectFn_zero]

theorem andFn_Tenum (n m : ℕ) :
    andFn (Tenum n) (Tenum m) = Tenum (andCode (min n 2) (min m 2)) := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m]
  have hn2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  have hm2 : min m 2 ≤ 2 := Nat.min_le_right m 2
  interval_cases (min n 2) <;> interval_cases (min m 2) <;>
    simp [Tenum, andCode, andFn_master, andFn_zero, andFn_one]

/-- **`andT` is a computable map** (relative to `prodPresentation Tpres Tpres` on the input side and
`Tpres` on the output side): its neighbourhood relation reduces, via `ofMap₂`'s unfolding and
`andFn_Tenum`, to the *decidable* `Tpres`-inclusion relation `X_{andCode (min n 2) (min m 2)} ⊆ Xₖ`,
hence is recursively decidable — a fortiori r.e. -/
theorem andT_isComputable : IsComputableMap (prodPresentation Tpres Tpres) Tpres andT := by
  have hcomp : Nat.Primrec (fun s : ℕ => Nat.pair
      (andCode (min s.unpair.1.unpair.1 2) (min s.unpair.1.unpair.2 2)) s.unpair.2) :=
    (primrec_andCode (primrec_min (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 2))
      (primrec_min (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.const 2))).pair
      Nat.Primrec.right
  have hdec : RecDecidable₂
      (fun t k => Tenum (andCode (min t.unpair.1 2) (min t.unpair.2 2)) ⊆ Tenum k) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m k, andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
      Tenum (andCode (min n 2) (min m 2)) ⊆ Tenum k := by
    intro n m k
    have hstep : andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
        andMap2.rel (Tenum n) (Tenum m) (Tenum k) := by
      show ((prod Example23.T Example23.T).mem (prodNbhd (Tenum n) (Tenum m)) ∧
        andMap2.rel (Sum.inl ⁻¹' prodNbhd (Tenum n) (Tenum m))
          (Sum.inr ⁻¹' prodNbhd (Tenum n) (Tenum m)) (Tenum k)) ↔ _
      rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      exact and_iff_right (prod_mem_prodNbhd (Tenum_mem n) (Tenum_mem m))
    rw [hstep]
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ Example23.T.mem (Tenum k) ∧
      andFn (Tenum n) (Tenum m) ⊆ Tenum k) ↔ _
    rw [andFn_Tenum n m]
    exact ⟨fun h => h.2.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, Tenum_mem k, h⟩⟩
  have key : RecDecidable₂
      (fun t k => andT.rel ((prodPresentation Tpres Tpres).X t) (Tpres.X k)) :=
    RecDecidable.of_iff (fun s => by
      show andT.rel ((prodPresentation Tpres Tpres).X s.unpair.1) (Tpres.X s.unpair.2) ↔ _
      rw [prodPresentation_X]
      exact hiff s.unpair.1.unpair.1 s.unpair.1.unpair.2 s.unpair.2) hdec
  exact key.re

/-! ### The general lifting engine: `postcompose` and `pointwiseBin`

Any computable `h : V₁ → V₂` lifts to a computable `(L → V₁) → (L → V₂)` (Scott's `postcompose`,
`curry (h ∘ eval)`), and any computable `h : V₀ × V₁ → V₂` lifts to a computable
`(L → V₀) × (L → V₁) → (L → V₂)` (`pointwiseBin`, evaluating both factors at the same argument and
applying `h`). Stating either against a *concrete* presentation of the relevant function space(s)
needs a bundle of characteristic functions for `funPresentation Lpres P`; `LFunData` packages
exactly that bundle, and `LFunData.ofPresentation` extracts one from an arbitrary
`P : ComputablePresentation V`, using `Classical.choice` exactly once per component presentation (to
pull concrete deciders out of `P.incl_computable`/`P.cons_computable`/`P.eq_computable`'s existentials
— the same classical bridge already used for `funSpace_isEffectivelyGiven`, just packaged so it can be
*named* and reused as data rather than immediately discharged into a `Prop` goal). -/

variable {β γ δ : Type*}


/-- **`postcompose` preserves computability.** If `h : V₁ → V₂` is computable, then so is
`postcompose h : (L → V₁) → (L → V₂)`, relative to any concrete function-space presentations built
from `LFunData` bundles: `eval` is computable (Theorem 7.5), composing with `h` stays computable
(Proposition 7.3), and `curry`-ing the result stays computable (Theorem 7.5 again). -/
theorem postcompose_isComputable {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    {P₁ : ComputablePresentation V₁} {P₂ : ComputablePresentation V₂}
    (d₁ : LFunData P₁) (d₂ : LFunData P₂) {h : ApproximableMap V₁ V₂}
    (hh : IsComputableMap P₁ P₂ h) :
    IsComputableMap d₁.pres d₂.pres (postcompose h) := by
  have heval : IsComputableMap (prodPresentation d₁.pres Lpres) P₁ (evalMap L V₁) :=
    evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
      d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p
  exact curry_isComputable d₁.pres Lpres P₂ d₂.gN d₂.incl0 d₂.incl1 d₂.eq1
    d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable heval hh)


/-- **`pointwiseBin` preserves computability.** If `h : V₀ × V₁ → V₂` is computable, then so is
`pointwiseBin h : (L → V₀) × (L → V₁) → (L → V₂)`, by the same composition-closure argument as
`postcompose` (projections, pairing, `eval`, and `curry` are all computable). -/
theorem pointwiseBin_isComputable {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ}
    {V₂ : NeighborhoodSystem δ} {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₂ : ComputablePresentation V₂} (d₀ : LFunData P₀) (d₁ : LFunData P₁) (d₂ : LFunData P₂)
    {h : ApproximableMap (prod V₀ V₁) V₂} (hh : IsComputableMap (prodPresentation P₀ P₁) P₂ h) :
    IsComputableMap (prodPresentation d₀.pres d₁.pres) d₂.pres (pointwiseBin h) := by
  have hπAB : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres)
      (prodPresentation d₀.pres d₁.pres) (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₀_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hπL : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) Lpres
      (proj₁ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₁_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hp0 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₀.pres
      (pwFst V₀ V₁) := comp_isComputable hπAB (proj₀_isComputable d₀.pres d₁.pres)
  have hp1 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₁.pres
      (pwSnd V₀ V₁) := comp_isComputable hπAB (proj₁_isComputable d₀.pres d₁.pres)
  have heval0 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₀
      ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp0 hπL)
      (evalMap_isComputable Lpres P₀ d₀.gN d₀.incl0 d₀.incl1 d₀.eq1
        d₀.hgN d₀.hgNp d₀.hincl0 d₀.hincl0p d₀.hincl1 d₀.hincl1p d₀.heq1 d₀.heq1p)
  have heval1 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₁
      ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp1 hπL)
      (evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
        d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p)
  exact curry_isComputable (prodPresentation d₀.pres d₁.pres) Lpres P₂ d₂.gN d₂.incl0 d₂.incl1
    d₂.eq1 d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable (paired_isComputable heval0 heval1) hh)

/-! ### Conclusion: the LUCID combinators `notT`/`andT` lift to computable `(L → T)` maps

One concrete choice of `LFunData Tpres` (`LTdata`, via `Classical.choice`) presents `(L → T)`
(`LTpres`); `notT`/`andT`'s computability (already established, choice-free) transports through
`postcompose`/`pointwiseBin` to give computable maps of exactly Scott's two stated types,
`(L→T) → (L→T)` and `(L→T) × (L→T) → (L→T)`. Since `comp_isComputable`/`paired_isComputable` close
computability under composition and pairing, **any** LUCID program built from these (and their kin,
built the same way from any other computable `T`-combinator) — however deeply composed — again
defines a computable map on `(L→T)`; `deMorganT_isComputable` below composes both lifted combinators
together (`¬(¬f ∧ ¬g)`, De Morgan's law for the sequential `and`) as a concrete witness of this
closure. -/


/-- **Exercise 7.24, fourth claim, `notT` case.** LUCID's pointwise negation lifts to a computable
map of type `(L→T) → (L→T)`. -/
theorem notT_lifted_isComputable : IsComputableMap LTpres LTpres (postcompose notT) :=
  postcompose_isComputable LTdata LTdata notT_isComputable

/-- **Exercise 7.24, fourth claim, `andT` case.** LUCID's pointwise (sequential) conjunction lifts to
a computable map of type `(L→T) × (L→T) → (L→T)`. -/
theorem andT_lifted_isComputable :
    IsComputableMap (prodPresentation LTpres LTpres) LTpres (pointwiseBin andT) :=
  pointwiseBin_isComputable LTdata LTdata LTdata andT_isComputable

/-- **A deeper LUCID program is still computable.** `deMorganT f g := ¬(¬f ∧ ¬g)` on `(L→T)`,
built by composing/pairing the two lifted combinators above (De Morgan's law for the sequential
`and`); it is computable purely by the closure lemmas `comp_isComputable`/`paired_isComputable`,
**with no fresh recursion-theoretic argument needed** — exactly Scott's "conclude that programs in
LUCID define computable maps." -/
theorem deMorganT_isComputable :
    IsComputableMap (prodPresentation LTpres LTpres) LTpres
      ((postcompose notT).comp (pointwiseBin andT)
        |>.comp (paired
          (postcompose notT |>.comp (proj₀ (funSpace L Example23.T) (funSpace L Example23.T)))
          (postcompose notT |>.comp (proj₁ (funSpace L Example23.T) (funSpace L Example23.T))))) :=
  comp_isComputable
    (paired_isComputable
      (comp_isComputable (proj₀_isComputable LTpres LTpres) notT_lifted_isComputable)
      (comp_isComputable (proj₁_isComputable LTpres LTpres) notT_lifted_isComputable))
    (comp_isComputable andT_lifted_isComputable notT_lifted_isComputable)
end DomainTheory.NeighbourhoodSystems.Exercise724
