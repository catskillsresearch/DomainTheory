/-ai
The neighbourhood system produced by the positive-system constructor is positive.

The positivity condition supplied to the constructor is the required witness.

The finite intersection of a sequence of sets is contained in each factor whose index is strictly below the length.

The proof is by induction on the length. Length zero has no such index. At a successor length the intersection is the intersection of the prefix with the last factor: the last index is contained on the right, and an earlier index is contained on the left and then by the inductive hypothesis.

If every term of a finite sequence is a neighbourhood and the sequence is consistent, then the finite intersection is a neighbourhood. This is Scott's extension of the intersection property from pairs to finite sequences.

The proof is by induction on the length. The empty intersection is the master neighbourhood. At a successor length the consistency witness is contained in the intersection of the prefix intersection with the last factor, so the prefix is consistent. The inductive hypothesis puts the prefix intersection in the system, the last factor is a neighbourhood, and one use of binary intersection closure finishes the step.

A finite sequence of neighbourhoods is consistent if and only if its finite intersection is a neighbourhood.

Consistency yields the intersection by the extension property. Conversely, once the intersection is a neighbourhood, it is a common lower bound of the sequence because it is contained in itself.

A filter contains the finite intersection of any finite sequence of its members.

The proof is by induction on the length. The empty intersection is the master, which belongs to the filter. The successor step is one binary intersection in the filter.

Given that every term is a neighbourhood, a filter contains the finite intersection if and only if it contains every term.

If the intersection belongs to the filter, upward closure along the containment of the intersection in each factor puts each term in the filter. The converse is closure of the filter under the finite intersection.

For two sequences of neighbourhoods, the limit families coincide if and only if the sequences are equivalent.

If the families coincide, each term of either sequence lies in its own limit family and hence in the other, so some term of the other sequence contains it. If the sequences are equivalent, a set in one limit family is contained in some term, and equivalence supplies a term of the other sequence contained in that term and therefore in the set.

The principal filter of a neighbourhood X lies below the principal filter of a neighbourhood Y if and only if Y is contained in X.

In one direction, X belongs to its own principal filter, so the inequality puts X in the principal filter of Y and reads off the containment. In the other direction a member of the principal filter of X lies above X and hence above Y.

The passage from a neighbourhood to its principal filter is injective.

Equality of the two principal filters gives both inclusions by the order characterization, and the two inclusions give equality of the neighbourhoods.

A neighbourhood Z belongs to a filter if and only if Z belongs to the principal filter of some member of the filter.

If Z belongs to the filter, it belongs to the principal filter of Z itself. If Z belongs to the principal filter of a member X, then X is contained in Z and upward closure puts Z in the filter.

A filter that has a least member, contained in every member, equals the principal filter of that member.

The two filters contain the same neighbourhoods. A member of the filter lies above the least member, so it belongs to the principal filter. A member of the principal filter lies above the least member and belongs to the filter by upward closure.

Isomorphism of a neighbourhood system with itself holds.

The identity order isomorphism is a witness.

Isomorphism of neighbourhood systems is symmetric.

The inverse of an order isomorphism is an order isomorphism.

Isomorphism of neighbourhood systems is transitive.

The composite of two order isomorphisms is an order isomorphism.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ofNestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.IsPositive
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ofPositive
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Consistent
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.limitFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.SeqEquiv
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.IsTotal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Isomorphic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ext
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_refl
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_trans
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.element_le_antisymm
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst34
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic.notation40

@[expose] public section

/-!
# Neighborhood systems (Scott 1981, PRG-19, §1) — foundations

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, Technical
Monograph PRG-19, Oxford (May 1981), Lecture I, *Domains given by neighbourhoods*.

Scott fixes a non-empty set `Δ` of *tokens* and considers a family `𝒟` of subsets of `Δ`
(the *neighbourhoods*). The order is *reversed* relative to information: a **smaller**
neighbourhood carries **more** information. A finite sequence of neighbourhoods is
*consistent* when it has a common lower bound inside `𝒟` (a `Z ∈ 𝒟` contained in all of
them); a neighbourhood system is closed under intersections of consistent finite sequences.

This file formalizes the very first page of §1:

* **Definition 1.1** — `NeighborhoodSystem`: a family with `Δ ∈ 𝒟` (condition (i)) and
  closure under consistent binary intersections (condition (ii)).
* **Factoid 1.1a / 1.1b** — Scott's recursive *convention* for the finite intersection
  `⋂_{i < n} Xᵢ` (`interUpTo`): the empty intersection is `Δ`, and the `(n+1)`-fold
  intersection peels off the last factor.
* **Theorem 1.1c** — "from (ii) we can extend the intersection property to any finite
  sequence", and *consequently* a finite sequence is consistent **iff** its intersection
  lies in `𝒟`.

The §1 core is deliberately **constructive**: Scott uses *partial* filters so that the
basic theory avoids maximal-filter existence (Zorn/choice). Every theorem here depends only
on `propext`/`Quot.sound` (no `Classical.choice`).
-/

namespace DomainTheory.NeighbourhoodSystems


/-- The system built by `ofPositive` is indeed positive. -/
theorem NeighborhoodSystem.ofPositive_isPositive {α : Type*} (mem : Set α → Prop)
    (master : Set α) (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_nonempty master_mem sub_master pos).IsPositive :=
  pos

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The finite intersection is contained in each of its factors: `⋂_{i < n} Xᵢ ⊆ Xⱼ` for
`j < n`. (Supporting lemma: this is what makes `⋂_{i < n} Xᵢ` a common lower bound of the
sequence, the intuition behind consistency.) -/
theorem interUpTo_subset (X : ℕ → Set α) :
    ∀ {n j : ℕ}, j < n → V.interUpTo X n ⊆ X j := by
  intro n
  induction n with
  | zero => intro j h; exact absurd h (Nat.not_lt_zero j)
  | succ n ih =>
    intro j h
    rw [interUpTo_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · subst h'; exact Set.inter_subset_right
    · exact Set.inter_subset_left.trans (ih h')


/-- **Theorem 1.1c (extension of the intersection property).** Scott: "from (ii), we can
extend the intersection property to any finite sequence." If `Xᵢ ∈ 𝒟` for every `i < n`
and the sequence is consistent, then the finite intersection `⋂_{i < n} Xᵢ` is again a
neighbourhood (`∈ 𝒟`). Proved by induction on `n`; the inductive step is one application of
condition (ii). -/
theorem interUpTo_mem (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → V.mem (X i)) → V.Consistent X n →
      V.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _ _; exact V.master_mem
  | succ n ih =>
    intro hX hcons
    obtain ⟨Z, hZmem, hZsub⟩ := hcons
    have hZsub' : Z ⊆ V.interUpTo X n ∩ X n := by rwa [interUpTo_succ] at hZsub
    -- The same witness `Z` shows the length-`n` prefix is consistent.
    have hconsn : V.Consistent X n :=
      ⟨Z, hZmem, hZsub'.trans Set.inter_subset_left⟩
    have hmemn : V.mem (V.interUpTo X n) :=
      ih (fun i hi => hX i (Nat.lt_succ_of_lt hi)) hconsn
    have hXn : V.mem (X n) := hX n (Nat.lt_succ_self n)
    rw [interUpTo_succ]
    exact V.inter_mem hmemn hXn hZmem hZsub'

/-- **Theorem 1.1c (consistency characterization).** "Consequently, `X₀, …, Xₙ₋₁` is
consistent in `𝒟` iff `⋂_{i < n} Xᵢ ∈ 𝒟`." (Given `Xᵢ ∈ 𝒟` for all `i < n`.)

* `→` is the extension property `interUpTo_mem`;
* `←` is immediate: the intersection is its own common lower bound. -/
theorem consistent_iff_interUpTo_mem (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ V.mem (V.interUpTo X n) := by
  constructor
  · exact V.interUpTo_mem X hX
  · intro h; exact ⟨V.interUpTo X n, h, Set.Subset.refl _⟩


/-- A filter (`Element`) is closed under the finite intersection `⋂_{i<n} Xᵢ`: if every factor
`Xᵢ` (`i < n`) lies in the filter `x`, so does `interUpTo X n`. Used in Exercises 1.18 and 1.21.
Base case `x.master_mem`; inductive step one `x.inter_mem`. -/
theorem Element.mem_interUpTo {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → x.mem (X i)) → x.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _; exact x.master_mem
  | succ n ih =>
    intro h
    rw [interUpTo_succ]
    exact x.inter_mem (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- Membership of the finite intersection in a filter, as a biconditional (given all factors
are neighbourhoods). `→` is upward closure along `interUpTo X n ⊆ Xᵢ` (`interUpTo_subset`); `←`
is `Element.mem_interUpTo`. -/
theorem Element.mem_interUpTo_iff {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) {n : ℕ} (hX : ∀ i, i < n → V.mem (X i)) :
    x.mem (V.interUpTo X n) ↔ ∀ i, i < n → x.mem (X i) := by
  constructor
  · intro h i hi
    exact x.up_mem h (hX i hi) (V.interUpTo_subset X hi)
  · exact x.mem_interUpTo X


/-- **Factoid 1.5b (Scott 1981, PRG-19).** "It is easy to prove that … the two families are
*equal* if and only if the sequences are *equivalent*." Given that every term of each sequence
is a neighbourhood, the limit families coincide exactly when the sequences are equivalent. -/
theorem limitFamily_eq_iff (X Y : ℕ → Set α)
    (hX : ∀ n, V.mem (X n)) (hY : ∀ m, V.mem (Y m)) :
    V.limitFamily X = V.limitFamily Y ↔ SeqEquiv X Y := by
  constructor
  · intro hEq
    refine ⟨fun m => ?_, fun n => ?_⟩
    · have hmem : Y m ∈ V.limitFamily Y := ⟨hY m, m, subset_rfl⟩
      rw [← hEq] at hmem
      obtain ⟨_, n, hn⟩ := hmem
      exact ⟨n, hn⟩
    · have hmem : X n ∈ V.limitFamily X := ⟨hX n, n, subset_rfl⟩
      rw [hEq] at hmem
      obtain ⟨_, m, hm⟩ := hmem
      exact ⟨m, hm⟩
  · rintro ⟨h1, h2⟩
    apply Set.ext
    intro Z
    constructor
    · rintro ⟨hZ, n, hn⟩
      obtain ⟨m, hm⟩ := h2 n
      exact ⟨hZ, m, hm.trans hn⟩
    · rintro ⟨hZ, m, hm⟩
      obtain ⟨n, hn⟩ := h1 m
      exact ⟨hZ, n, hn.trans hm⟩


/-- **Factoid 1.7a (Scott 1981, PRG-19) — inclusion-*reversing*.** "It is obvious that the
correspondence between `X` and `↑X` is one-one and inclusion *reversing*." The order on `↑`:
`↑X ⊑ ↑Y ↔ Y ⊆ X` (equivalently Scott's `X ⊆ Y ↔ ↑Y ⊑ ↑X`).

`→` tests at `Z = X` (`X ∈ ↑X` since `X ⊆ X`), reading off `Y ⊆ X` from `X ∈ ↑Y`; `←` chains
`Y ⊆ X ⊆ Z`. -/
theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

/-- **Factoid 1.7a (Scott 1981, PRG-19) — one-one.** The correspondence `X ↦ ↑X` is injective:
`↑X = ↑Y ⟹ X = Y`. Antisymmetry applied to `principal_le_iff` in both directions. -/
theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

/-- **Factoid 1.7b (Scott 1981, PRG-19).** "It is also obvious from the definitions that for each
`x ∈ |𝒟|`, `x = ⋃ {↑X ∣ X ∈ x}`." In membership form (the union over a `Set (Set α)` made
concrete): a neighbourhood `Z` is in `x` iff `Z` lies in the principal filter `↑X` of *some*
member `X` of `x`.

`→` uses `X = Z` (`Z ∈ ↑Z` as `Z ⊆ Z`); `←` is upward closure `up_mem` (`X ⊆ Z`, `Z ∈ 𝒟`). -/
theorem eq_iUnion_principal (x : V.Element) {Z : Set α} :
    x.mem Z ↔ ∃ X, ∃ hX : x.mem X, (V.principal (x.sub hX)).mem Z := by
  constructor
  · intro hZ
    exact ⟨Z, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨X, hX, hVZ, hXZ⟩
    exact x.up_mem hX hVZ hXZ


/-- **Factoid 1.8b (Scott 1981, PRG-19) — "Examples 1.2–1.5 revisited".** "Any explicitly given
filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." Stated honestly: if
the filter `x` has a `⊆`-minimum member `X` (one contained in every member of `x`), then `x` is
exactly the principal filter `↑X`. In a *finite* system every filter has such a minimum (the
intersection of its finitely many members, itself in `x` by closure), so every element is
principal; that finiteness step is the only classical ingredient and is left implicit here — this
constructive core captures the content.

`⊆`: any `Z ∈ x` satisfies `X ⊆ Z` by minimality, so `Z ∈ ↑X`. `⊇`: `Z ∈ ↑X` means `Z ∈ 𝒟` and
`X ⊆ Z`, so `Z ∈ x` by upward closure from `X ∈ x`. -/
theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem


/-- `≅ᴰ` is reflexive (`OrderIso.refl`). -/
theorem Isomorphic.refl {α : Type*} (V : NeighborhoodSystem α) : V ≅ᴰ V :=
  ⟨OrderIso.refl _⟩

/-- `≅ᴰ` is symmetric (`OrderIso.symm`). -/
theorem Isomorphic.symm {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h : V₀ ≅ᴰ V₁) : V₁ ≅ᴰ V₀ :=
  h.elim fun e => ⟨e.symm⟩

/-- `≅ᴰ` is transitive (`OrderIso.trans`). -/
theorem Isomorphic.trans {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} (h₀ : V₀ ≅ᴰ V₁) (h₁ : V₁ ≅ᴰ V₂) : V₀ ≅ᴰ V₂ :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨e₀.trans e₁⟩

end DomainTheory.NeighbourhoodSystems
