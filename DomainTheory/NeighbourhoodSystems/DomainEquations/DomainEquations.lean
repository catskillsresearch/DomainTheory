module


public import DomainTheory.NeighbourhoodSystems.DomainConstructs.DomainConstructs
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.FixedPointsAndRecursion
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.MappingsBetweenDomains
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.TypedLambdaCalculus
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic


@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
export CategoryTheory (Category)

open scoped CategoryTheory


scoped notation "𝟙" => CategoryTheory.CategoryStruct.id
end

section
variable {α : Type*}

/- concordance: source L3799 DEFINITION 6.10 subdomain -/
/-- **Definition 6.10 (Scott 1981, PRG-19).** The *subsystem* (subdomain) relation `D ◁ E` for two
neighbourhood systems over the same token type. It records that `D` and `E` are systems over the
same `Δ` (`master_eq`), that `D` is a subfamily of `E` (`sub`), and — the essential clause — that
consistency is inherited from `E`: an intersection of two `D`-neighbourhoods that happens to be an
`E`-neighbourhood is already a `D`-neighbourhood (`inter_closed`). -/
structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  /-- `D` and `E` are systems over the same set of tokens `Δ`. -/
  master_eq : D.master = E.master
  /-- `D ⊆ E`: every neighbourhood of `D` is a neighbourhood of `E`. -/
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  /-- Consistency in `D` is the same as in `E`: if `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`. -/
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)
end

section
variable {α : Type*}

@[inherit_doc] infix:50 " ◁ " => Subsystem
end

section
variable {α : Type*}

namespace Subsystem

/-- Two neighbourhood systems with the same `mem` and the same `master` are equal (the remaining
fields of `NeighborhoodSystem` are `Prop`s). -/
theorem _root_.DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D = E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

/-- The subsystem relation is **transitive**: `D ◁ E` and `E ◁ F` give `D ◁ F`.

The `inter_closed` clause threads through `E`: from `X, Y ∈ D ⊆ E` and `X ∩ Y ∈ F`, the relation
`E ◁ F` puts `X ∩ Y ∈ E`, and then `D ◁ E` puts `X ∩ Y ∈ D`. -/
theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

/-- **Scott's remark (the prose after Definition 6.10).** Once `D₀` and `D₁` both sit inside a
common system `E` as subdomains, the subdomain relation between them is just inclusion of
neighbourhood families: `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`.

* `→` is the `sub` clause of `D₀ ◁ D₁`.
* `←` builds `D₀ ◁ D₁` from `D₀ ⊆ D₁`: the masters agree because both equal `E`'s master, and
  the `inter_closed` clause routes through `E` — an intersection `X ∩ Y` of `D₀`-neighbourhoods
  lying in `D₁` lies in `E` (since `D₁ ⊆ E`), and `D₀ ◁ E` then returns it to `D₀`. -/
theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
end

section
-- DomainObj.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

/-- An object of the category of domains: a token type together with a neighbourhood system on it. -/
structure DomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system (the "domain"). -/
  sys : NeighborhoodSystem carrier

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- The master neighbourhood `Γ = {1,2}* 0 Δ` of `D^§`: any path, `D`-token in `Δ`. -/
def Gamma (D : NeighborhoodSystem α) : Set (List Bool × α) := {t | t.2 ∈ D.master}

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `1P = {(1::p, a) ∣ (p, a) ∈ P}`: the `1`-prefixed copy of a `D^§`-neighbourhood `P`. -/
def embL (P : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ p', t.1 = true :: p' ∧ (p', t.2) ∈ P}

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `2Q = {(2::q, a) ∣ (q, a) ∈ Q}`: the `2`-prefixed copy of a `D^§`-neighbourhood `Q`. -/
def embR (Q : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ q', t.1 = false :: q' ∧ (q', t.2) ∈ Q}

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `1P ∪ 2Q`: the product-style neighbourhood of `D^§`. -/
def embPair (P Q : Set (List Bool × α)) : Set (List Bool × α) := embL P ∪ embR Q

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `0X = {([], a) ∣ a ∈ X}`: the `0`-tagged copy of a `D`-neighbourhood `X` (empty `{1,2}`-path). -/
def embZero (X : Set α) : Set (List Bool × α) := {t | t.1 = [] ∧ t.2 ∈ X}

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/- concordance: source L3218 EXAMPLE 6.1 indefinite product -/
/-- **Example 6.1 (Scott 1981, PRG-19).** The neighbourhoods of `D^§`, defined inductively as the
*least* family of subsets of `Γ` containing (i) `Γ`, (ii) `0X` for `X ∈ 𝒟`, and (iii) `1P ∪ 2Q`
whenever it already contains `P` and `Q`. This is Scott's fixed-point family
`𝒟^§ = {Γ} ∪ {0X ∣ X ∈ 𝒟} ∪ {1P ∪ 2Q ∣ P, Q ∈ 𝒟^§}`. -/
inductive MemS (D : NeighborhoodSystem α) : Set (List Bool × α) → Prop
  | gamma : MemS D (Gamma D)
  | zero {X : Set α} : D.mem X → MemS D (embZero X)
  | pair {P Q : Set (List Bool × α)} : MemS D P → MemS D Q → MemS D (embPair P Q)

end Example61
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- `bX = {b :: w' ∣ w' ∈ X}`: the `b`-prefixed copy of a neighbourhood `X` (Scott's `0X` for
`b = false` and `1X` for `b = true`). -/
def embBit (b : Bool) (X : Set Str) : Set Str := {w | ∃ w', w = b :: w' ∧ w' ∈ X}

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem mem_embBit {b : Bool} {X : Set Str} {w : Str} :
    w ∈ embBit b X ↔ ∃ w', w = b :: w' ∧ w' ∈ X := Iff.rfl

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- Scott's standing assumption `∅ ∉ B`: every neighbourhood of `B` is nonempty (cones contain their
generating prefix). -/
theorem B_nonempty : ∀ X, B.mem X → X.Nonempty := by
  rintro X ⟨σ, rfl⟩; exact ⟨σ, List.prefix_rfl⟩

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- The right-hand side of Scott's domain equation: the sum system `B + B` (Exercise 3.18). -/
abbrev BB : NeighborhoodSystem (Option (Str ⊕ Str)) := sum B B B_nonempty B_nonempty

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- `bX = b·X` is exactly the single-bit prepend of Example 1.B. -/
theorem embBit_eq_prepend (b : Bool) (X : Set Str) : embBit b X = prepend [b] X := by
  ext w
  simp only [mem_embBit, mem_prepend]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨τ, hX, rfl⟩; exact ⟨τ, rfl, hX⟩

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- `b(σΣ*) = (bσ)Σ*`: prepending a bit to a cone gives the cone of the longer prefix. -/
theorem embBit_cone (b : Bool) (σ : Str) : embBit b (cone σ) = cone (b :: σ) := by
  rw [embBit_eq_prepend, prepend_cone]; rfl

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_inter (b : Bool) (X X' : Set Str) :
    embBit b X ∩ embBit b X' = embBit b (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩
    exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_inter_ne {b b' : Bool} (h : b ≠ b') (X Y : Set Str) :
    embBit b X ∩ embBit b' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq
  exact h heq.1

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_ne {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty) :
    embBit b X ≠ embBit b' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (b :: w') ∈ embBit b' Y := heq ▸ (⟨w', rfl, hw'⟩ : (b :: w') ∈ embBit b X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he
  exact h he.1

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_subset {b : Bool} {X X' : Set Str} :
    embBit b X ⊆ embBit b X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact hX'
  · rintro h w ⟨w', rfl, hX⟩
    exact ⟨w', rfl, h hX⟩

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_injective {b : Bool} {X X' : Set Str} (h : embBit b X = embBit b X') : X = X' :=
  Set.Subset.antisymm (embBit_subset.mp h.subset) (embBit_subset.mp h.symm.subset)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/- concordance: source L3510 EXAMPLE 6.2 sequence domain equations -/
/-- **Example 6.2 — the shape of a `B`-neighbourhood.** Every neighbourhood of `B` is either the
master `Σ* = cone []`, a `0`-copy `0X` with `X ∈ B`, or a `1`-copy `1X` with `X ∈ B`. -/
theorem memB_cases {W : Set Str} (hW : B.mem W) :
    W = Set.univ ∨ (∃ X, B.mem X ∧ W = embBit false X) ∨ (∃ Y, B.mem Y ∧ W = embBit true Y) := by
  obtain ⟨σ, rfl⟩ := hW
  cases σ with
  | nil => exact Or.inl cone_nil
  | cons b σ' =>
    cases b with
    | false => exact Or.inr (Or.inl ⟨cone σ', memB_cone σ', (embBit_cone false σ').symm⟩)
    | true => exact Or.inr (Or.inr ⟨cone σ', memB_cone σ', (embBit_cone true σ').symm⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- Prepending a bit lands back in `B`. -/
theorem memB_embBit (b : Bool) {X : Set Str} (hX : B.mem X) : B.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact memB_prepend [b] hX

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- If `bW ∈ B` then `W ∈ B`: a `b`-prefixed neighbourhood that lands in `B` must be `b·(cone w')`,
so `W = cone w'`. -/
theorem memB_embBit_inv {b : Bool} {W : Set Str} (h : B.mem (embBit b W)) : B.mem W := by
  obtain ⟨σ, hσ⟩ := h
  have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
  obtain ⟨w', rfl, -⟩ := hmem
  rw [← embBit_cone] at hσ
  rw [embBit_injective hσ]
  exact memB_cone w'

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem nil_not_mem_embBit {b : Bool} {X : Set Str} : ([] : Str) ∉ embBit b X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_ne_univ (b : Bool) (X : Set Str) : embBit b X ≠ Set.univ := by
  intro h; exact nil_not_mem_embBit (X := X) (b := b) (by rw [h]; trivial)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_inj₀_inv {X : Set Str} (h : BB.mem (inj₀ X)) : B.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := B_nonempty Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_inj₁_inv {Y : Set Str} (h : BB.mem (inj₁ Y)) : B.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := B_nonempty X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : BB.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (B_nonempty X hX)
  · exact inj₁_nonempty (B_nonempty Y hY)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 — forward half of `B ≅ B + B`.** An element `x` of `B` is sent to the sum element
recording, for each branch, whether `x` reaches the `0`-copy `0X` (left summand) or the `1`-copy `1Y`
(right summand). -/
def toBB (x : B.Element) : BB.Element where
  mem W := W = sumMaster B B
    ∨ (∃ X, B.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, B.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (memB_embBit false hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (memB_embBit true hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem toBB_mem_inj₀ {x : B.Element} {X : Set Str} (hX : B.mem X) :
    (toBB x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := B_nonempty X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem toBB_mem_inj₁ {x : B.Element} {Y : Set Str} (hY : B.mem Y) :
    (toBB x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := B_nonempty X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 — inverse half of `B ≅ B + B`.** -/
def fromBB (s : BB.Element) : B.Element where
  mem W := W = Set.univ
    ∨ (∃ X, B.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, B.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact ⟨[], cone_nil.symm⟩
    · exact memB_embBit false hX
    · exact memB_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem fromBB_mem_embF {s : BB.Element} {X : Set Str} (hX : B.mem X) :
    (fromBB s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem fromBB_mem_embT {s : BB.Element} {Y : Set Str} (hY : B.mem Y) :
    (fromBB s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem fromBB_toBB (x : B.Element) : fromBB (toBB x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toBB_mem_inj₀ hX).mp hs
    · exact (toBB_mem_inj₁ hY).mp hs
  · intro hW
    rcases memB_cases (x.sub hW) with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toBB_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toBB_mem_inj₁ hY).mpr hW⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem toBB_fromBB (s : BB.Element) : toBB (fromBB s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromBB_mem_embF hX).mp hs
    · exact (fromBB_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromBB_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromBB_mem_embT hY).mpr hW⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|B| ≃o |B + B|`.** -/
def bbEquiv : B.Element ≃o BB.Element where
  toFun := toBB
  invFun := fromBB
  left_inv := fromBB_toBB
  right_inv := toBB_fromBB
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases memB_cases (x.sub hX) with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toBB_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toBB_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62


/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `B ≅ B + B`.** Scott's binary-sequence
domain `B` is, as a domain, isomorphic to `B + B`: a sequence is bottom, or begins with `0`, or begins
with `1`, the two non-bottom cases giving the two summands. -/
theorem B_domain_equation : B ≅ᴰ sum B B B_nonempty B_nonempty :=
  ⟨bbEquiv⟩

end Example62
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62


theorem embBit_nonempty {b : Bool} {X : Set Str} (hX : X.Nonempty) : (embBit b X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨b :: w', w', rfl, hw'⟩

end Example62
end

namespace Example62A
open NeighborhoodSystem ApproximableMap ExampleB

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- The slot prefix `i 1ʲ 0`: the leading tag bit `i` (Scott's `+/−`), then `j` ones, then a zero.
Reaching component `j` of the tag-`i` tuple means matching this prefix. -/
def slotPre (i : Bool) (j : ℕ) : Str := i :: (List.replicate j true ++ [false])
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Scott's tag-`i` tuple neighbourhood** `i ⋃_{j<n} 1ʲ0 X_j`: the union of the `n` slots, slot `j`
holding `X j` behind the prefix `i 1ʲ 0`. (For `i = false`/`true` these are Scott's left/right
copies, the `−`/`+` summands.) -/
def embTuple (i : Bool) (X : Fin n → Set Str) : Set Str :=
  {w | ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j}
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Scott's domain `A`** as the *least* family of subsets of `Σ* = {0,1}*` containing (i) the master
`Σ*` and (ii) every tag-`i` tuple `i ⋃_{j<n} 1ʲ0 X_j` built from components `X j` already in `A`:

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A }`. -/
inductive MemA (n : ℕ) : Set Str → Prop
  | univ : MemA n Set.univ
  | tuple (i : Bool) {X : Fin n → Set Str} : (∀ j, MemA n (X j)) → MemA n (embTuple i X)
end

section
variable {β : Type*} {n : ℕ}

/-- The *proper product* neighbourhood `⋃_{j<n} {j} × X_j`: token `(j, b)` lies in it iff `b ∈ X_j`.
This is the `n`-ary analogue of `prodNbhd` (Definition 3.1). -/
def prodN (X : Fin n → Set β) : Set (Fin n × β) := {p | p.2 ∈ X p.1}
end

section
variable {β : Type*} {n : ℕ}

@[simp] theorem mem_prodN {X : Fin n → Set β} {p : Fin n × β} : p ∈ prodN X ↔ p.2 ∈ X p.1 := Iff.rfl
end

section
variable {β : Type*} {n : ℕ}

theorem prodN_injective {X X' : Fin n → Set β} (h : prodN X = prodN X') : ∀ j, X j = X' j := by
  intro j; ext b
  have := Set.ext_iff.mp h (j, b)
  simpa only [mem_prodN] using this
end

section
variable {β : Type*} {n : ℕ}

theorem prodN_inter {X X' : Fin n → Set β} :
    prodN X ∩ prodN X' = prodN (fun j => X j ∩ X' j) := by
  ext p; simp only [Set.mem_inter_iff, mem_prodN]
end

section
variable {β : Type*} {n : ℕ}

theorem prodN_subset {X X' : Fin n → Set β} : prodN X ⊆ prodN X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j b hb; exact h (show (j, b) ∈ prodN X from hb)
  · intro h p hp; exact h p.1 hp
end

section
variable {β : Type*} {n : ℕ}

/-- **The positive `n`-fold product `Vⁿ`** of a neighbourhood system `V`, over `Fin n × β`.
The assumption `0 < n` is necessary because Scott's token set `Fin n × Δ` must be non-empty.
Its neighbourhoods are exactly the proper products `prodN X` with each component `X j ∈ V`;
closure under intersection is componentwise. -/
def npow (V : NeighborhoodSystem β) (n : ℕ) (hn : 0 < n) : NeighborhoodSystem (Fin n × β) where
  mem W := ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X
  master := prodN (fun _ => V.master)
  master_nonempty := by
    obtain ⟨b, hb⟩ := V.master_nonempty
    exact ⟨(⟨0, hn⟩, b), hb⟩
  master_mem := ⟨_, fun _ => V.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩ ⟨Zw, hZw, rfl⟩ hsub
    refine ⟨fun j => X j ∩ X' j, ?_, prodN_inter⟩
    intro j
    rw [prodN_inter] at hsub
    exact V.inter_mem (hX j) (hX' j) (hZw j) (prodN_subset.mp hsub j)
  sub_master := by
    rintro W ⟨X, hX, rfl⟩
    exact prodN_subset.mpr (fun j => V.sub_master (hX j))
end

section
variable {β : Type*} {n : ℕ}

@[simp] theorem npow_mem {V : NeighborhoodSystem β} {W : Set (Fin n × β)} {hn : 0 < n} :
    (npow V n hn).mem W ↔ ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X := Iff.rfl
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem mem_embTuple {i : Bool} {X : Fin n → Set Str} {w : Str} :
    w ∈ embTuple i X ↔ ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j := Iff.rfl
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_nonempty {i : Bool} {X : Fin n → Set Str} (j : Fin n) (h : (X j).Nonempty) :
    (embTuple i X).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨slotPre i (j : ℕ) ++ a, j, a, rfl, ha⟩
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- Under `0 < n` every neighbourhood of `A` is non-empty (Scott's `∅ ∉ A`). -/
theorem memA_nonempty (hn : 0 < n) : ∀ {W}, MemA n W → W.Nonempty := by
  intro W hW
  induction hW with
  | univ => exact ⟨[], Set.mem_univ []⟩
  | tuple i hX ih => exact embTuple_nonempty ⟨0, hn⟩ (ih ⟨0, hn⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem nil_not_mem_embTuple {i : Bool} {X : Fin n → Set Str} : ([] : Str) ∉ embTuple i X := by
  rintro ⟨j, a, heq, -⟩
  rw [slotPre, List.cons_append] at heq
  exact List.cons_ne_nil _ _ heq.symm
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_ne_univ {i : Bool} (X : Fin n → Set Str) : embTuple i X ≠ Set.univ := by
  intro h
  have : ([] : Str) ∈ embTuple i X := by rw [h]; exact Set.mem_univ []
  exact nil_not_mem_embTuple this
end

section
variable {β : Type*} {n : ℕ}

/-- Under Scott's standing assumption `∅ ∉ V`, no neighbourhood of `Vⁿ` is empty (provided `0 < n`,
so there is a coordinate to witness). -/
theorem npow_nonempty {V : NeighborhoodSystem β} (hn : 0 < n)
    (hV : ∀ X, V.mem X → X.Nonempty) : ∀ W, (npow V n hn).mem W → W.Nonempty := by
  rintro W ⟨X, hX, rfl⟩
  obtain ⟨b, hb⟩ := hV (X ⟨0, hn⟩) (hX ⟨0, hn⟩)
  exact ⟨(⟨0, hn⟩, b), hb⟩
end

section
variable {β : Type*} {n : ℕ}

/-- Parsing the `1ʲ0` body: the position of the first `false` pins down `j` and the remainder. -/
theorem slot_list_inj : ∀ (j j' : ℕ) (u v : Str),
    List.replicate j true ++ false :: u = List.replicate j' true ++ false :: v → j = j' ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, j' + 1, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, u, v, h => by
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
        List.cons.injEq] at h
      obtain ⟨hj, hu⟩ := slot_list_inj j j' u v h.2
      exact ⟨by rw [hj], hu⟩
end

section
variable {β : Type*} {n : ℕ}

/-- **Uniqueness of slot decomposition.** A token `i 1ʲ 0 u` determines the tag `i`, the index `j`,
and the remainder `u`. This is what makes the slots pairwise disjoint. -/
theorem slotPre_inj {i i' : Bool} {j j' : ℕ} {u v : Str}
    (h : slotPre i j ++ u = slotPre i' j' ++ v) : i = i' ∧ j = j' ∧ u = v := by
  rw [slotPre, slotPre, List.cons_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨hi, hrest⟩ := h
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append] at hrest
  obtain ⟨hj, huv⟩ := slot_list_inj j j' u v hrest
  exact ⟨hi, hj, huv⟩
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_inter {i : Bool} (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i X' = embTuple i (fun j => X j ∩ X' j) := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple]
  constructor
  · rintro ⟨⟨j, a, rfl, ha⟩, ⟨j', a', heq, ha'⟩⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ⟨j, a, rfl, ha, ha'⟩
  · rintro ⟨j, a, rfl, ha, ha'⟩
    exact ⟨⟨j, a, rfl, ha⟩, ⟨j, a, rfl, ha'⟩⟩
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_inter_ne {i i' : Bool} (h : i ≠ i') (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i' X' = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨j, a, rfl, ha⟩ ⟨j', a', heq, ha'⟩
  exact h (slotPre_inj heq).1
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_ne {i i' : Bool} (h : i ≠ i') {X Y : Fin n → Set Str} (j : Fin n)
    (hX : (X j).Nonempty) : embTuple i X ≠ embTuple i' Y := by
  intro heq
  obtain ⟨a, ha⟩ := hX
  have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' Y := heq ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
  obtain ⟨j', a', he, -⟩ := hmem
  exact h (slotPre_inj he).1
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_subset {i : Bool} {X X' : Fin n → Set Str} :
    embTuple i X ⊆ embTuple i X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j a ha
    obtain ⟨j', a', heq, ha'⟩ := h ⟨j, a, rfl, ha⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ha'
  · rintro h w ⟨j, a, rfl, ha⟩
    exact ⟨j, a, rfl, h j ha⟩
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem embTuple_injective {i : Bool} {X X' : Fin n → Set Str}
    (h : embTuple i X = embTuple i X') : ∀ j, X j = X' j := by
  intro j
  exact Set.Subset.antisymm (embTuple_subset.mp h.subset j) (embTuple_subset.mp h.symm.subset j)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- Inversion: the components of a tuple-shaped neighbourhood of `A` are themselves in `A`. -/
theorem memA_tuple_inv (hn : 0 < n) {i : Bool} {X : Fin n → Set Str}
    (h : MemA n (embTuple i X)) : ∀ j, MemA n (X j) := by
  generalize hW : embTuple i X = W at h
  cases h with
  | univ =>
    exfalso
    have : ([] : Str) ∈ embTuple i X := by rw [hW]; exact Set.mem_univ []
    exact nil_not_mem_embTuple this
  | @tuple i' X' hX' =>
    have hne : (embTuple i' X').Nonempty :=
      embTuple_nonempty ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩))
    rw [← hW] at hne
    obtain ⟨w, j, a, rfl, ha⟩ := hne
    have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' X' := hW ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
    obtain ⟨j', a', he, -⟩ := hmem
    have hii : i = i' := (slotPre_inj he).1
    subst hii
    intro k; rw [embTuple_injective hW k]; exact hX' k
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- A non-empty witness contained in a tag-`i'` tuple must carry the tag `i'`. -/
theorem tag_eq_of_subset (hn : 0 < n) {i i' : Bool} {Z V : Fin n → Set Str}
    (hZ : ∀ j, MemA n (Z j)) (hsub : embTuple i Z ⊆ embTuple i' V) : i = i' := by
  obtain ⟨a, ha⟩ := memA_nonempty hn (hZ ⟨0, hn⟩)
  obtain ⟨j', v, he, -⟩ := hsub ⟨⟨0, hn⟩, a, rfl, ha⟩
  exact (slotPre_inj he).1
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **`A` is closed under consistent intersection.** Scott's verification, by induction on the way `X`
entered `A`: the cross case `embTuple false · ∩ embTuple true ·` collapses to `∅` (killed by the
non-empty witness), the same-tag case combines componentwise (recursing on the consistency witness's
slots). -/
theorem memA_inter (hn : 0 < n) :
    ∀ {X}, MemA n X → ∀ {Y}, MemA n Y → ∀ {Z}, MemA n Z → Z ⊆ X ∩ Y → MemA n (X ∩ Y) := by
  intro X hX
  induction hX with
  | univ =>
    intro Y hY Z _ _
    rw [Set.univ_inter]; exact hY
  | @tuple i X hX ih =>
    intro Y hY Z hZ hsub
    cases hY with
    | univ =>
      rw [Set.inter_univ]; exact MemA.tuple i hX
    | @tuple i' X' hX' =>
      by_cases hii : i = i'
      · rw [hii, embTuple_inter] at hsub ⊢
        cases hZ with
        | univ => exact absurd (hsub (Set.mem_univ [])) nil_not_mem_embTuple
        | @tuple i'' ZW hZW =>
          have htag : i'' = i' := tag_eq_of_subset hn hZW hsub
          rw [htag] at hsub
          have hZsub := embTuple_subset.mp hsub
          exact MemA.tuple i' (fun j => ih j (hX' j) (hZW j) (hZsub j))
      · rw [embTuple_inter_ne hii] at hsub ⊢
        exfalso
        obtain ⟨z, hz⟩ := memA_nonempty hn hZ
        exact Set.notMem_empty z (hsub hz)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Scott's domain `A`** packaged as a neighbourhood system over `{0,1}*` (needs `0 < n`). -/
def Asys (n : ℕ) (hn : 0 < n) : NeighborhoodSystem Str where
  mem := MemA n
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := MemA.univ
  inter_mem := fun hX hY hZ hsub => memA_inter hn hX hY hZ hsub
  sub_master := fun _ => Set.subset_univ _
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem Asys_mem {hn : 0 < n} {W : Set Str} : (Asys n hn).mem W ↔ MemA n W := Iff.rfl
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem Asys_master {hn : 0 < n} : (Asys n hn).master = Set.univ := rfl
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- The `n`-fold product `Aⁿ = npow A n`. -/
abbrev Apow (hn : 0 < n) : NeighborhoodSystem (Fin n × Str) := npow (Asys n hn) n hn
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem apowNe (hn : 0 < n) : ∀ W, (Apow hn).mem W → W.Nonempty :=
  npow_nonempty hn (fun _ h => memA_nonempty hn h)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- The right-hand side of Scott's equation: the separated sum `Aⁿ + Aⁿ`. -/
abbrev AAsys (hn : 0 < n) : NeighborhoodSystem (Option ((Fin n × Str) ⊕ (Fin n × Str))) :=
  sum (Apow hn) (Apow hn) (apowNe hn) (apowNe hn)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem aa_mem_inj₀_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₀ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := apowNe hn _ hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem aa_mem_inj₁_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₁ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := apowNe hn _ hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem aa_mem_nonempty (hn : 0 < n) {W : Set (Option ((Fin n × Str) ⊕ (Fin n × Str)))}
    (h : (AAsys hn).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (apowNe hn _ hX)
  · exact inj₁_nonempty (apowNe hn _ hY)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem apow_mem_prodN (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (Apow hn).mem (prodN X) := ⟨X, hX, rfl⟩
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem aa_mem_inj₀ (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (AAsys hn).mem (inj₀ (prodN X)) := Or.inr (Or.inl ⟨prodN X, apow_mem_prodN hn hX, rfl⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem aa_mem_inj₁ (hn : 0 < n) {Y : Fin n → Set Str} (hY : ∀ j, MemA n (Y j)) :
    (AAsys hn).mem (inj₁ (prodN Y)) := Or.inr (Or.inr ⟨prodN Y, apow_mem_prodN hn hY, rfl⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem apow_mem_prodN_inv (hn : 0 < n) {X : Fin n → Set Str} (h : (Apow hn).mem (prodN X)) :
    ∀ j, MemA n (X j) := by
  obtain ⟨X', hX', heq⟩ := h
  intro j; rw [prodN_injective heq j]; exact hX' j
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Forward half of `A ≅ Aⁿ + Aⁿ`.** An element `z` of `A` is sent to the sum element recording, for
each branch, whether `z` reaches the left copy `0X` (left summand `Aⁿ`) or the right copy `1Y` (right
summand `Aⁿ`). -/
def toAA (hn : 0 < n) (z : (Asys n hn).Element) : (AAsys hn).Element where
  mem W := W = sumMaster (Apow hn) (Apow hn)
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = inj₀ (prodN X) ∧ z.mem (embTuple false X))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = inj₁ (prodN Y) ∧ z.mem (embTuple true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact (AAsys hn).master_mem
    · exact aa_mem_inj₀ hn hX
    · exact aa_mem_inj₁ hn hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ (apow_mem_prodN hn hX')], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ (apow_mem_prodN hn hY')], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_comm, sumMaster_inter_inj₀ (apow_mem_prodN hn hX)], hzX⟩)
    · refine Or.inr (Or.inl ⟨fun j => X j ∩ X' j, ?_, by rw [inj₀_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embTuple_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embTuple_inter_ne (by decide : (false : Bool) ≠ true)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (apow_mem_prodN hn hY)], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embTuple_inter_ne (by decide : (true : Bool) ≠ false)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j, ?_, by rw [inj₁_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embTuple_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X', hX', rfl⟩ := hV'
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemA.tuple false hX')
          (embTuple_subset.mpr (prodN_subset.mp (inj₀_subset_inj₀.mp hsub)))
      · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
        exact absurd (hsub (il_mem_inj₀.mpr hb)) il_mem_inj₁
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := apowNe hn (prodN Y) (apow_mem_prodN hn hY)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨Y', hY', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact z.up_mem hzY (MemA.tuple true hY')
          (embTuple_subset.mpr (prodN_subset.mp (inj₁_subset_inj₁.mp hsub)))
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem toAA_mem_inj₀ (hn : 0 < n) {z : (Asys n hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (toAA hn z).mem (inj₀ (prodN X)) ↔ z.mem (embTuple false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rw [funext (prodN_injective (inj₀_injective heq))]; exact hz
    · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
      exact absurd (heq ▸ il_mem_inj₀.mpr hb) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem toAA_mem_inj₁ (hn : 0 < n) {z : (Asys n hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (toAA hn z).mem (inj₁ (prodN Y)) ↔ z.mem (embTuple true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := apowNe hn (prodN X') (apow_mem_prodN hn hX')
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rw [funext (prodN_injective (inj₁_injective heq))]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Inverse half of `A ≅ Aⁿ + Aⁿ`.** -/
def fromAA (hn : 0 < n) (s : (AAsys hn).Element) : (Asys n hn).Element where
  mem W := W = Set.univ
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = embTuple false X ∧ s.mem (inj₀ (prodN X)))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = embTuple true Y ∧ s.mem (inj₁ (prodN Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact MemA.univ
    · exact MemA.tuple false hX
    · exact MemA.tuple true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · have hs := s.inter_mem hsX hsX'
      rw [inj₀_inter, prodN_inter] at hs
      exact Or.inr (Or.inl ⟨fun j => X j ∩ X' j,
        apow_mem_prodN_inv hn (aa_mem_inj₀_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · have hs := s.inter_mem hsY hsY'
      rw [inj₁_inter, prodN_inter] at hs
      exact Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j,
        apow_mem_prodN_inv hn (aa_mem_inj₁_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : false = i'' := tag_eq_of_subset hn hX hsub
        subst htag
        refine Or.inr (Or.inl ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsX (aa_mem_inj₀ hn hV)
          (inj₀_subset_inj₀.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : true = i'' := tag_eq_of_subset hn hY hsub
        subst htag
        refine Or.inr (Or.inr ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsY (aa_mem_inj₁ hn hV)
          (inj₁_subset_inj₁.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem fromAA_mem_embF (hn : 0 < n) {s : (AAsys hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (fromAA hn s).mem (embTuple false X) ↔ s.mem (inj₀ (prodN X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ X)
    · rw [funext (embTuple_injective heq)]; exact hs
    · exact absurd heq
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX ⟨0, hn⟩)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

@[simp] theorem fromAA_mem_embT (hn : 0 < n) {s : (AAsys hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (fromAA hn s).mem (embTuple true Y) ↔ s.mem (inj₁ (prodN Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ Y)
    · exact absurd heq.symm
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩)))
    · rw [funext (embTuple_injective heq)]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem fromAA_toAA (hn : 0 < n) (z : (Asys n hn).Element) : fromAA hn (toAA hn z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toAA_mem_inj₀ hn hX).mp hs
    · exact (toAA_mem_inj₁ hn hY).mp hs
  · intro hW
    cases z.sub hW with
    | univ => exact Or.inl rfl
    | @tuple i X hX =>
      cases i with
      | false => exact Or.inr (Or.inl ⟨X, hX, rfl, (toAA_mem_inj₀ hn hX).mpr hW⟩)
      | true => exact Or.inr (Or.inr ⟨X, hX, rfl, (toAA_mem_inj₁ hn hX).mpr hW⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

theorem toAA_fromAA (hn : 0 < n) (s : (AAsys hn).Element) : toAA hn (fromAA hn s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromAA_mem_embF hn hX).mp hs
    · exact (fromAA_mem_embT hn hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, hX, rfl⟩ := hV
      exact Or.inr (Or.inl ⟨X, hX, rfl, (fromAA_mem_embF hn hX).mpr hW⟩)
    · obtain ⟨Y, hY, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromAA_mem_embT hn hY).mpr hW⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **The isomorphism `|A| ≃o |Aⁿ + Aⁿ|`.** -/
def aaEquiv (hn : 0 < n) : (Asys n hn).Element ≃o (AAsys hn).Element where
  toFun := toAA hn
  invFun := fromAA hn
  left_inv := fromAA_toAA hn
  right_inv := toAA_fromAA hn
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      cases z.sub hW with
      | univ => exact z'.master_mem
      | @tuple i X hX =>
        cases i with
        | false => exact (toAA_mem_inj₀ hn hX).mp (h _ (Or.inr (Or.inl ⟨X, hX, rfl, hW⟩)))
        | true => exact (toAA_mem_inj₁ hn hX).mp (h _ (Or.inr (Or.inr ⟨X, hX, rfl, hW⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)
end

section
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `A ≅ Aⁿ + Aⁿ`.** Scott's "simple, yet
interesting generalization of `B`": the domain `A` over `{0,1}*` (whose non-`⊥` elements are the two
copies — left `−` and right `+` — of an `n`-tuple of elements of `A`) is isomorphic to the separated
sum `Aⁿ + Aⁿ` of two copies of its own `n`-fold cartesian power. -/
theorem A_domain_equation (hn : 0 < n) : Asys n hn ≅ᴰ AAsys hn := ⟨aaEquiv hn⟩
end

end Example62A
open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

section
/-- Left tag `0a = some (inl a)`. -/
def t0 {α β γ : Type*} (a : α) : Option (α ⊕ β ⊕ γ) := some (Sum.inl a)
end

section
/-- The tagged left copy `0X`. -/
def j0 {α β γ : Type*} (X : Set α) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ a, w = t0 a ∧ a ∈ X}
end

section
variable {α β γ : Type*}

@[simp] theorem t0_mem_j0 {X : Set α} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∈ j0 X ↔ a ∈ X := by
  constructor
  · rintro ⟨a', heq, ha'⟩; simp only [t0, Option.some.injEq, Sum.inl.injEq] at heq; exact heq ▸ ha'
  · intro ha; exact ⟨a, rfl, ha⟩
end

section
/-- Middle tag `1b = some (inr (inl b))`. -/
def t1 {α β γ : Type*} (b : β) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inl b))
end

section
/-- The tagged middle copy `1Y`. -/
def j1 {α β γ : Type*} (Y : Set β) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ b, w = t1 b ∧ b ∈ Y}
end

section
variable {α β γ : Type*}

@[simp] theorem t1_mem_j1 {Y : Set β} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∈ j1 Y ↔ b ∈ Y := by
  constructor
  · rintro ⟨b', heq, hb'⟩
    simp only [t1, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at heq; exact heq ▸ hb'
  · intro hb; exact ⟨b, rfl, hb⟩
end

section
/-- Right tag `2c = some (inr (inr c))`. -/
def t2 {α β γ : Type*} (c : γ) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inr c))
end

section
/-- The tagged right copy `2Z`. -/
def j2 {α β γ : Type*} (Z : Set γ) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ c, w = t2 c ∧ c ∈ Z}
end

section
variable {α β γ : Type*}

@[simp] theorem t2_mem_j2 {Z : Set γ} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∈ j2 Z ↔ c ∈ Z := by
  constructor
  · rintro ⟨c', heq, hc'⟩
    simp only [t2, Option.some.injEq, Sum.inr.injEq] at heq; exact heq ▸ hc'
  · intro hc; exact ⟨c, rfl, hc⟩
end

section
variable {α β γ : Type*}

@[simp] theorem none_not_mem_j0 {X : Set α} : (none : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0])
end

section
variable {α β γ : Type*}

@[simp] theorem none_not_mem_j1 {Y : Set β} : (none : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1])
end

section
variable {α β γ : Type*}

@[simp] theorem none_not_mem_j2 {Z : Set γ} : (none : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t2])
end

section
variable {α β γ : Type*}

@[simp] theorem t1_not_mem_j0 {X : Set α} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t1])
end

section
variable {α β γ : Type*}

@[simp] theorem t2_not_mem_j0 {X : Set α} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t2])
end

section
variable {α β γ : Type*}

@[simp] theorem t0_not_mem_j1 {Y : Set β} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t0, t1])
end

section
variable {α β γ : Type*}

@[simp] theorem t2_not_mem_j1 {Y : Set β} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1, t2])
end

section
variable {α β γ : Type*}

@[simp] theorem t0_not_mem_j2 {Z : Set γ} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t0, t2])
end

section
variable {α β γ : Type*}

@[simp] theorem t1_not_mem_j2 {Z : Set γ} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t1, t2])
end

section
variable {α β γ : Type*}

theorem j0_inter_j0 (X X' : Set α) :
    (j0 X ∩ j0 X' : Set (Option (α ⊕ β ⊕ γ))) = j0 (X ∩ X') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, t0, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j0_inter_j1 (X : Set α) (Y : Set β) :
    (j0 X ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j1, t0, t1, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j0_inter_j2 (X : Set α) (Z : Set γ) :
    (j0 X ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j2, t0, t2, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j0_nonempty {X : Set α} (hX : X.Nonempty) : (j0 X : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨t0 a, a, rfl, ha⟩
end

section
variable {α β γ : Type*}

theorem j0_subset_j0 {X X' : Set α} :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ j0 X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact t0_mem_j0.mp (h (t0_mem_j0.mpr ha))
  · rintro h w ⟨a, rfl, ha⟩; exact t0_mem_j0.mpr (h ha)
end

section
variable {α β γ : Type*}

theorem j1_inter_j1 (Y Y' : Set β) :
    (j1 Y ∩ j1 Y' : Set (Option (α ⊕ β ⊕ γ))) = j1 (Y ∩ Y') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, t1, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j1_inter_j2 (Y : Set β) (Z : Set γ) :
    (j1 Y ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, j2, t1, t2, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j1_nonempty {Y : Set β} (hY : Y.Nonempty) : (j1 Y : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨b, hb⟩ := hY; exact ⟨t1 b, b, rfl, hb⟩
end

section
variable {α β γ : Type*}

theorem j1_subset_j1 {Y Y' : Set β} :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ j1 Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact t1_mem_j1.mp (h (t1_mem_j1.mpr hb))
  · rintro h w ⟨b, rfl, hb⟩; exact t1_mem_j1.mpr (h hb)
end

section
variable {α β γ : Type*}

theorem j1_injective {Y Y' : Set β}
    (h : (j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y') : Y = Y' :=
  Set.Subset.antisymm (j1_subset_j1.mp h.subset) (j1_subset_j1.mp h.symm.subset)
end

section
variable {α β γ : Type*}

theorem j2_inter_j2 (Z Z' : Set γ) :
    (j2 Z ∩ j2 Z' : Set (Option (α ⊕ β ⊕ γ))) = j2 (Z ∩ Z') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j2, t2, Set.mem_inter_iff]
end

section
variable {α β γ : Type*}

theorem j2_nonempty {Z : Set γ} (hZ : Z.Nonempty) : (j2 Z : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨c, hc⟩ := hZ; exact ⟨t2 c, c, rfl, hc⟩
end

section
variable {α β γ : Type*}

theorem j2_subset_j2 {Z Z' : Set γ} :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ j2 Z' ↔ Z ⊆ Z' := by
  constructor
  · intro h c hc; exact t2_mem_j2.mp (h (t2_mem_j2.mpr hc))
  · rintro h w ⟨c, rfl, hc⟩; exact t2_mem_j2.mpr (h hc)
end

section
variable {α β γ : Type*}

theorem j2_injective {Z Z' : Set γ}
    (h : (j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z') : Z = Z' :=
  Set.Subset.antisymm (j2_subset_j2.mp h.subset) (j2_subset_j2.mp h.symm.subset)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

/-- The master neighbourhood of the three-way sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`. -/
def master3 : Set (Option (α ⊕ β ⊕ γ)) :=
  insert none (j0 V₀.master ∪ j1 V₁.master ∪ j2 V₂.master)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

@[simp] theorem none_mem_master3 : (none : Option (α ⊕ β ⊕ γ)) ∈ master3 V₀ V₁ V₂ :=
  Set.mem_insert _ _
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- Scott's standing assumption `∅ ∉ C`: every neighbourhood of `C` is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- `b{σ} = {bσ}`: prepending a bit to a singleton. -/
theorem embBit_singleton (b : Bool) (σ : Str) : embBit b ({σ} : Set Str) = {(b :: σ : Str)} := by
  rw [embBit_eq_prepend, Example44.prepend_singleton]; rfl

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem eq_master3_of_subset {W : Set (Option (α ⊕ β ⊕ γ))}
    (hsub : master3 V₀ V₁ V₂ ⊆ W) (hsub' : W ⊆ master3 V₀ V₁ V₂) : W = master3 V₀ V₁ V₂ :=
  Set.Subset.antisymm hsub' hsub
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem j0_subset_master3 {X : Set α} (hX : V₀.mem X) :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨a, rfl, ha⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_left _ (t0_mem_j0.mpr (V₀.sub_master hX ha)))))
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem j1_subset_master3 {Y : Set β} (hY : V₁.mem Y) :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨b, rfl, hb⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_right _ (t1_mem_j1.mpr (V₁.sub_master hY hb)))))
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem j2_subset_master3 {Z : Set γ} (hZ : V₂.mem Z) :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨c, rfl, hc⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ (t2_mem_j2.mpr (V₂.sub_master hZ hc))))
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem master3_inter_j0 {X : Set α} (hX : V₀.mem X) :
    (master3 V₀ V₁ V₂ ∩ j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X :=
  Set.inter_eq_right.mpr (j0_subset_master3 hX)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem master3_inter_j1 {Y : Set β} (hY : V₁.mem Y) :
    (master3 V₀ V₁ V₂ ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y :=
  Set.inter_eq_right.mpr (j1_subset_master3 hY)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

theorem master3_inter_j2 {Z : Set γ} (hZ : V₂.mem Z) :
    (master3 V₀ V₁ V₂ ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z :=
  Set.inter_eq_right.mpr (j2_subset_master3 hZ)
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 — the shape of a `C`-neighbourhood.** Every neighbourhood of `C` is the master
`Σ* = cone []`, the terminator `{Λ} = {[]}`, a `0`-copy `0X` with `X ∈ C`, or a `1`-copy `1X`. -/
theorem memC_cases {W : Set Str} (hW : C.mem W) :
    W = Set.univ ∨ W = ({[]} : Set Str)
      ∨ (∃ X, C.mem X ∧ W = embBit false X) ∨ (∃ Y, C.mem Y ∧ W = embBit true Y) := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl cone_nil
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨cone σ', memC_cone σ', (embBit_cone false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨cone σ', memC_cone σ', (embBit_cone true σ').symm⟩))
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨{σ'}, memC_singleton σ', (embBit_singleton false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨{σ'}, memC_singleton σ', (embBit_singleton true σ').symm⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- Prepending a bit lands back in `C`. -/
theorem memC_embBit (b : Bool) {X : Set Str} (hX : C.mem X) : C.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact Example44.memC_prepend [b] hX

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- If `bW ∈ C` then `W ∈ C`. -/
theorem memC_embBit_inv {b : Bool} {W : Set Str} (h : C.mem (embBit b W)) : C.mem W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_cone] at hσ; rw [embBit_injective hσ]; exact memC_cone w'
  · have hmem : σ ∈ embBit b W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set Str))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_singleton] at hσ; rw [embBit_injective hσ]; exact memC_singleton w'

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem singleton_nil_inter_embBit (b : Bool) (X : Set Str) :
    (({[]} : Set Str) ∩ embBit b X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embBit, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩
  exact absurd heq (by simp)

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem singleton_nil_ne_embBit (b : Bool) (X : Set Str) : ({[]} : Set Str) ≠ embBit b X := by
  intro h
  exact nil_not_mem_embBit (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Str) ∈ ({[]} : Set Str)))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem singleton_nil_ne_univ : ({[]} : Set Str) ≠ Set.univ := by
  intro h
  have hmem : ([true] : Str) ∈ ({[]} : Set Str) := h ▸ Set.mem_univ _
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

/-- **Example 6.2 — the three-way separated sum `D₀ + D₁ + D₂`** over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`,
under the standing assumption that no neighbourhood of any factor is empty. -/
def sum3 (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (h₂ : ∀ Z, V₂.mem Z → Z.Nonempty) : NeighborhoodSystem (Option (α ⊕ β ⊕ γ)) where
  mem W := W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
    ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)
  master := master3 V₀ V₁ V₂
  master_nonempty := ⟨none, none_mem_master3⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
    · exact subset_rfl
    · exact j0_subset_master3 hX
    · exact j1_subset_master3 hY
    · exact j2_subset_master3 hZ
  inter_mem := by
    have hne : ∀ W, (W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
        ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)) →
        (W : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
      · exact ⟨none, none_mem_master3⟩
      · exact j0_nonempty (h₀ X hX)
      · exact j1_nonempty (h₁ Y hY)
      · exact j2_nonempty (h₂ Z hZ)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Zc, hZc, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [master3_inter_j0 hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [master3_inter_j1 hY']; exact Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl⟩))
      · rw [master3_inter_j2 hZ']; exact Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl⟩))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j0 hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [j0_inter_j0] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ0 (j0_subset_j0.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j1 hY]; exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j1_inter_j1] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · exact Or.inr (Or.inr (Or.inl ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ1 (j1_subset_j1.mp hZsub), rfl⟩))
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j2 hZc]; exact Or.inr (Or.inr (Or.inr ⟨Zc, hZc, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [Set.inter_comm, j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j2_inter_j2] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · exact Or.inr (Or.inr (Or.inr ⟨Zc ∩ Z', V₂.inter_mem hZc hZ' hZ2 (j2_subset_j2.mp hZsub), rfl⟩))
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- `𝟙` is positive: its single neighbourhood `univ` (over the inhabited `Unit`) is nonempty. -/
theorem unitSys_nonempty : ∀ X, unitSys.mem X → X.Nonempty := by
  rintro X rfl; exact Set.univ_nonempty

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- The right-hand side of the domain equation: the three-way sum `𝟙 + C + C`. -/
abbrev CC : NeighborhoodSystem (Option (Unit ⊕ Str ⊕ Str)) :=
  sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem sum3_mem_j1_inv {X : Set Str} (h : CC.mem (j1 X)) : C.mem X := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Y, hY, heq⟩ | ⟨Z, hZ, heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · rw [j1_injective heq]; exact hY
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem sum3_mem_j2_inv {Y : Set Str} (h : CC.mem (j2 Y)) : C.mem Y := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Z, hZ, heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t1_mem_j1.mpr hc)) t1_not_mem_j2
  · rw [j2_injective heq]; exact hY'

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem sum3_mem_nonempty {W : Set (Option (Unit ⊕ Str ⊕ Str))} (h : CC.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨U, hU, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (unitSys_nonempty U hU)
  · exact j1_nonempty (C_nonempty Y hY)
  · exact j2_nonempty (C_nonempty Z hZ)

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 — forward half of `C ≅ 𝟙 + C + C`.** -/
def toCC (x : C.Element) : CC.Element where
  mem W := W = master3 unitSys C C
    ∨ (W = j0 (Set.univ : Set Unit) ∧ x.mem ({[]} : Set Str))
    ∨ (∃ X, C.mem X ∧ W = j1 X ∧ x.mem (embBit false X))
    ∨ (∃ Y, C.mem Y ∧ W = j2 Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Set.univ, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨X', hX', rfl, hzF'⟩ | ⟨Y', hY', rfl, hzT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨master3_inter_j0 rfl, hzU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', master3_inter_j1 hX', hzF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', master3_inter_j2 hY', hzT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, master3_inter_j0 rfl], hzU⟩)
    · refine Or.inr (Or.inl ⟨?_, hzU⟩)
      rw [j0_inter_j0, Set.inter_self]
    · exfalso
      have hx := x.inter_mem hzU hzF'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzU hzT'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, master3_inter_j1 hX], hzF⟩))
    · exfalso
      have hx := x.inter_mem hzF hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, j1_inter_j1 X X', ?_⟩))
      · have hx := x.inter_mem hzF hzF'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzF hzF'; rwa [embBit_inter] at hx
    · exfalso
      have hx := x.inter_mem hzF hzT'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j2 hY], hzT⟩))
    · exfalso
      have hx := x.inter_mem hzT hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzT hzF'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, j2_inter_j2 Y Y', ?_⟩))
      · have hx := x.inter_mem hzT hzT'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzT hzT'; rwa [embBit_inter] at hx
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub (CC.sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain rfl := hX'; exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · refine Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl, ?_⟩))
        exact x.up_mem hzF (memC_embBit false hY') (embBit_subset.mpr (j1_subset_j1.mp hsub))
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · refine Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl, ?_⟩))
        exact x.up_mem hzT (memC_embBit true hZ') (embBit_subset.mpr (j2_subset_j2.mp hsub))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem toCC_mem_j0 {x : C.Element} :
    (toCC x).mem (j0 (Set.univ : Set Unit)) ↔ x.mem ({[]} : Set Str) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · exact hz
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem toCC_mem_j1 {x : C.Element} {X : Set Str} (hX : C.mem X) :
    (toCC x).mem (j1 X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heq ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j0
    · rw [j1_injective heqj]; exact hz
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heqj ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · intro hz; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hz⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem toCC_mem_j2 {x : C.Element} {Y : Set Str} (hY : C.mem Y) :
    (toCC x).mem (j2 Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j0
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heqj ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1
    · rw [j2_injective heqj]; exact hz
  · intro hz; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 — inverse half of `C ≅ 𝟙 + C + C`.** -/
def fromCC (s : CC.Element) : C.Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set Str) ∧ s.mem (j0 (Set.univ : Set Unit)))
    ∨ (∃ X, C.mem X ∧ W = embBit false X ∧ s.mem (j1 X))
    ∨ (∃ Y, C.mem Y ∧ W = embBit true Y ∧ s.mem (j2 Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl ⟨[], cone_nil.symm⟩
    · exact memC_singleton []
    · exact memC_embBit false hX
    · exact memC_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨X', hX', rfl, hsF'⟩ | ⟨Y', hY', rfl, hsT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsU hsT'; rw [j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsF⟩))
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, embBit_inter false X X', ?_⟩))
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs
        exact sum3_mem_j1_inv (s.sub hs)
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs; exact hs
    · exfalso
      have hs := s.inter_mem hsF hsT'; rw [j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsT⟩))
    · exfalso
      have hs := s.inter_mem hsT hsU'; rw [Set.inter_comm, j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsT hsF'; rw [Set.inter_comm, j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, embBit_inter true Y Y', ?_⟩))
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs
        exact sum3_mem_j2_inv (s.sub hs)
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        have hm := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · refine Or.inr (Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩))
        exact s.up_mem hsF (Or.inr (Or.inr (Or.inl ⟨X', hX', rfl⟩)))
          (j1_subset_j1.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        have hm := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩))
        exact s.up_mem hsT (Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl⟩)))
          (j2_subset_j2.mpr (embBit_subset.mp hsub))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem fromCC_mem_nil {s : CC.Element} :
    (fromCC s).mem ({[]} : Set Str) ↔ s.mem (j0 (Set.univ : Set Unit)) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embBit false X')
    · exact absurd heq (singleton_nil_ne_embBit true Y')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem fromCC_mem_embF {s : CC.Element} {X : Set Str} (hX : C.mem X) :
    (fromCC s).mem (embBit false X) ↔ s.mem (j1 X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · exact absurd heq.symm (singleton_nil_ne_embBit false X)
    · rw [embBit_injective heqj]; exact hs
    · exact absurd heqj (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X hX))
  · intro hs; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hs⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem fromCC_mem_embT {s : CC.Element} {Y : Set Str} (hY : C.mem Y) :
    (fromCC s).mem (embBit true Y) ↔ s.mem (j2 Y) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (singleton_nil_ne_embBit true Y)
    · exact absurd heqj.symm (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X' hX'))
    · rw [embBit_injective heqj]; exact hs
  · intro hs; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem fromCC_toCC (x : C.Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_j0.mp hs
    · exact (toCC_mem_j1 hX).mp hs
    · exact (toCC_mem_j2 hY).mp hs
  · intro hW
    rcases memC_cases (x.sub hW) with rfl | rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_j0.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (toCC_mem_j1 hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (toCC_mem_j2 hY).mpr hW⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

theorem toCC_fromCC (s : CC.Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embF hX).mp hs
    · exact (fromCC_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨U, hU, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · obtain rfl := hU
      exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (fromCC_mem_embF hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (fromCC_mem_embT hY).mpr hW⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|C| ≃o |𝟙 + C + C|`.** -/
def ccEquiv : C.Element ≃o CC.Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hW
      rcases memC_cases (x.sub hW) with rfl | rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_j0.mp (h _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_j1 hA).mp (h _ (Or.inr (Or.inr (Or.inl ⟨A, hA, rfl, hW⟩))))
      · exact (toCC_mem_j2 hA).mp (h _ (Or.inr (Or.inr (Or.inr ⟨A, hA, rfl, hW⟩))))
    · intro h W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h _ hz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, h _ hz⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, h _ hz⟩))

end Example62C
end

section
variable {α β γ : Type*}
variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
variable {V₀ V₁ V₂}

namespace Example62C


/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `C ≅ {{Λ}} + C + C`.** Scott's domain
`C` of finite-or-infinite binary sequences is, as a domain, isomorphic to the three-way separated sum
`𝟙 + C + C`: a sequence is bottom, the finished empty sequence `Λ` (the `𝟙` summand), or begins with
`0` or `1` (the two `C` summands). -/
theorem C_domain_equation :
    C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty :=
  ⟨ccEquiv⟩

end Example62C
end

section
variable {α β γ : Type*}

theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)
end

namespace Example62Regular
open Language

section
variable {n : ℕ}

/-- A **total tree** over the alphabet `Σ = Fin n` (Scott's `n`-ary `±` tree): an assignment of a
`±` label (`Bool`, `true = +`) to every node, addressed by a finite selector `σ ∈ Σ*`. A tree is
*total* in Scott's sense (every node carries a genuine label), as opposed to the partial elements of
the domain `A` of `Example62A.lean` where labels may be `⊥`. -/
abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool
end

section
variable {n : ℕ}

/-- Scott's `pos : A → T`: the `±` label at the **root** of the tree (`pos(±⟨…⟩) = true/false`). -/
def pos (a : Tree n) : Bool := a []
end

section
variable {n : ℕ}

/-- Scott's subtree selector `σ ↦ aσ`: the subtree of `a` reached by the selector `σ`. Defined so
that `(aσ)τ = a(στ)`; the `pos`-label at node `τ` of `aσ` is the label at node `στ` of `a`. -/
def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)
end

section
variable {n : ℕ}

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl
end

section
variable {n : ℕ}

/-- The `i`-th immediate subtree `aᵢ = a i` (Scott's children of the root node). -/
def child (a : Tree n) (i : Fin n) : Tree n := select a [i]
end

section
variable {n : ℕ}

@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp
end

section
variable {n : ℕ}

@[simp] theorem pos_select (a : Tree n) (σ : List (Fin n)) : pos (select a σ) = a σ := by
  simp [pos]
end

section
variable {n : ℕ}

/-- **Scott's language of a tree.** `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` — the selectors that land on a
`+` node. Equivalently (by `pos_select`) the set of `σ` with `a σ = true`. A `Language (Fin n)` is
just a set of words over the alphabet, exactly Scott's "language". -/
def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}
end

section
variable {n : ℕ}

@[simp] theorem mem_treeLang {a : Tree n} {σ : List (Fin n)} : σ ∈ treeLang a ↔ a σ = true := Iff.rfl
end

section
variable {n : ℕ}

/-- **Eventual periodicity (Scott).** A tree `a` is *eventually periodic* iff the set of its subtrees
`{aσ ∣ σ ∈ Σ*}` is finite. (Equivalently — by the picture — the tree is built from finitely many
distinct subtrees, so it is "ultimately periodic" along every branch.) -/
def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite
end

section
variable {n : ℕ}

/-- Composing selectors: `a(στ) = (aσ)τ`. -/
theorem select_append (a : Tree n) (σ τ : List (Fin n)) :
    select a (σ ++ τ) = select (select a σ) τ := by
  funext ρ; simp [List.append_assoc]
end

section
variable {n : ℕ}

/-- **Scott's selector recursion, step `a(iσ) = (aᵢ)σ`.** Reading the digit `i` then `σ` is the same
as descending to the `i`-th child `aᵢ` and reading `σ` there. -/
theorem select_cons (a : Tree n) (i : Fin n) (σ : List (Fin n)) :
    select a (i :: σ) = select (child a i) σ := by
  funext τ; simp [child]
end

section
variable {n : ℕ}

/-- `L_a` is genuinely `{σ ∣ pos(aσ) = true}` as Scott writes it. -/
theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl
end

section
variable {n : ℕ}

/-- The label function recovers the tree from its language, so `treeLang` is **one-one**: two trees
with the same language are the same tree (a node's `±` label is recorded by whether its selector is
in the language). -/
theorem treeLang_injective : Function.Injective (treeLang (n := n)) := by
  intro a a' h
  funext σ
  have hmem : (σ ∈ treeLang a) ↔ (σ ∈ treeLang a') := by rw [h]
  simp only [mem_treeLang] at hmem
  cases ha : a σ <;> cases ha' : a' σ <;> simp_all
end

section
variable {n : ℕ}

/-- **The subtree is the left quotient.** `L_{aσ} = σ⁻¹ L_a`: the language of the subtree reached by
reading `σ` is exactly the *left quotient* of `L_a` by `σ` (the residual / "state after reading
`σ`"). This is the heart of Scott's "`a` is the initial state, `aσ` the state after reading `σ`". -/
theorem treeLang_select (a : Tree n) (σ : List (Fin n)) :
    treeLang (select a σ) = (treeLang a).leftQuotient σ := by
  ext τ
  simp only [mem_treeLang, select_apply, Language.mem_leftQuotient]
end

section
variable {n : ℕ}

/-- **Scott's closing claim, made precise (Example 6.2).** A tree's language `L_a` is a *regular
event* of automata theory **iff** the tree is eventually periodic. This is the Myhill–Nerode theorem
in disguise: the subtrees `aσ` are the left quotients `σ⁻¹ L_a` (`treeLang_select`), so "finitely many
subtrees" is "finitely many left quotients", which Myhill–Nerode equates with regularity. -/
theorem eventuallyPeriodic_iff_isRegular (a : Tree n) :
    EventuallyPeriodic a ↔ (treeLang a).IsRegular := by
  have hcomp : (treeLang a).leftQuotient = treeLang ∘ select a :=
    funext fun σ => (treeLang_select a σ).symm
  rw [Language.isRegular_iff_finite_range_leftQuotient, hcomp, Set.range_comp]
  exact (Set.finite_image_iff (treeLang_injective.injOn)).symm
end

section
variable {n : ℕ}

/-- The inverse half of Scott's claim: **every regular event arises** as the language of an eventually
periodic tree. Concretely, take the tree whose root labels record membership in `L`; reading a tape
`σ` lands on the residual language `σ⁻¹ L`, of which there are finitely many exactly when `L` is
regular. -/
theorem isRegular_iff_exists_eventuallyPeriodic (L : Language (Fin n)) :
    L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L := by
  classical
  constructor
  · intro hL
    refine ⟨fun σ => decide (σ ∈ L), ?_, ?_⟩
    · have hlang : treeLang (fun σ => decide (σ ∈ L)) = L := by
        ext σ; simp only [mem_treeLang, decide_eq_true_eq]
      rw [eventuallyPeriodic_iff_isRegular, hlang]; exact hL
    · ext σ; simp only [mem_treeLang, decide_eq_true_eq]
  · rintro ⟨a, hEP, rfl⟩
    exact (eventuallyPeriodic_iff_isRegular a).mp hEP
end

end Example62Regular
open NeighborhoodSystem ApproximableMap Example62 ExampleB

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The master neighbourhood `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` of the concrete sum. -/
def sumTokMaster (D₀ D₁ : NeighborhoodSystem Str) : Set Str :=
  insert [] (embBit false D₀.master ∪ embBit true D₁.master)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embF_subset_sumTokMaster {X : Set Str} (hX : D₀.mem X) :
    embBit false X ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₀.sub_master hX)).trans (Set.subset_union_left.trans (Set.subset_insert _ _))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embT_subset_sumTokMaster {Y : Set Str} (hY : D₁.mem Y) :
    embBit true Y ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₁.sub_master hY)).trans (Set.subset_union_right.trans (Set.subset_insert _ _))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem nil_mem_sumTokMaster : ([] : Str) ∈ sumTokMaster D₀ D₁ := Set.mem_insert _ _

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embF_ne_sumTokMaster {X : Set Str} : embBit false X ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embT_ne_sumTokMaster {Y : Set Str} : embBit true Y ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem sumTokMaster_inter_embF {X : Set Str} (hX : D₀.mem X) :
    sumTokMaster D₀ D₁ ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_sumTokMaster hX)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem sumTokMaster_inter_embT {Y : Set Str} (hY : D₁.mem Y) :
    sumTokMaster D₀ D₁ ∩ embBit true Y = embBit true Y :=
  Set.inter_eq_right.mpr (embT_subset_sumTokMaster hY)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/- concordance: source L4087 EXERCISE 6.19 strict sum and product -/
/-- **Exercise 6.19 — the concrete sum system `𝒟₀ + 𝒟₁` over `{0,1}*`.** A neighbourhood is the
master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`, a left copy `0X` (`X ∈ 𝒟₀`), or a right copy `1Y` (`Y ∈ 𝒟₁`). The standing
assumption `∅ ∉ 𝒟ᵢ` (`h₀`, `h₁`) makes the two tagged copies disjoint, so the system is closed under
consistent intersection. -/
def sumTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub), rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embF {X : Set Str} (hX : D₀.mem X) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embF_inv {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem (embBit false W)) :
    D₀.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩ | ⟨Y, hY, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX
  · exact absurd heq.symm (embBit_ne (show (true : Bool) ≠ false by decide) (h₁ Y hY))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embT_inv {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩ | ⟨Y, hY, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_nonempty {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_inj₀_inv {X : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₀ X)) : D₀.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := h₁ Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_inj₁_inv {Y : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₁ Y)) : D₁.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : (sum D₀ D₁ h₀ h₁).mem W) :
    W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (h₀ X hX)
  · exact inj₁_nonempty (h₁ Y hY)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The forward half of the isomorphism, a token-level analogue of `Example62.toBB`. -/
def toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : (sum D₀ D₁ h₀ h₁).Element where
  mem W := W = sumMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, D₁.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact sumTok_mem_embF_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact sumTok_mem_embT_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (sumTok_mem_embF hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (sumTok_mem_embT hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem toSum_mem_inj₀ {x : (sumTok D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (toSum x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := h₀ X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem toSum_mem_inj₁ {x : (sumTok D₀ D₁ h₀ h₁).Element} {Y : Set Str} (hY : D₁.mem Y) :
    (toSum x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := h₀ X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The inverse half of the isomorphism, a token-level analogue of `Example62.fromBB`. -/
def fromSum (s : (sum D₀ D₁ h₀ h₁).Element) : (sumTok D₀ D₁ h₀ h₁).Element where
  mem W := W = sumTokMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, D₁.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((sumTok D₀ D₁ h₀ h₁).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fromSum_mem_embF {s : (sum D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (fromSum s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fromSum_mem_embT {s : (sum D₀ D₁ h₀ h₁).Element} {Y : Set Str} (hY : D₁.mem Y) :
    (fromSum s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem fromSum_toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : fromSum (toSum x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toSum_mem_inj₀ hX).mp hs
    · exact (toSum_mem_inj₁ hY).mp hs
  · intro hW
    rcases x.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toSum_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toSum_mem_inj₁ hY).mpr hW⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- A product neighbourhood `{Λ} ∪ 0X ∪ 1Y` over `{0,1}*`. -/
def prodTokNbhd (X Y : Set Str) : Set Str := insert [] (embBit false X ∪ embBit true Y)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_prodTokNbhd_nil {X Y : Set Str} : ([] : Str) ∈ prodTokNbhd X Y :=
  Set.mem_insert _ _

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_prodTokNbhd_false {X Y : Set Str} {w' : Str} :
    (false :: w') ∈ prodTokNbhd X Y ↔ w' ∈ X := by
  simp only [prodTokNbhd, Set.mem_insert_iff, Set.mem_union, mem_embBit]
  constructor
  · rintro (h | ⟨u, hu, hX⟩ | ⟨u, hu, hY⟩)
    · exact absurd h (by simp)
    · rw [List.cons.injEq] at hu; rw [hu.2]; exact hX
    · rw [List.cons.injEq] at hu; exact absurd hu.1 (by decide)
  · intro h; exact Or.inr (Or.inl ⟨w', rfl, h⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_prodTokNbhd_true {X Y : Set Str} {w' : Str} :
    (true :: w') ∈ prodTokNbhd X Y ↔ w' ∈ Y := by
  simp only [prodTokNbhd, Set.mem_insert_iff, Set.mem_union, mem_embBit]
  constructor
  · rintro (h | ⟨u, hu, hX⟩ | ⟨u, hu, hY⟩)
    · exact absurd h (by simp)
    · rw [List.cons.injEq] at hu; exact absurd hu.1 (by decide)
    · rw [List.cons.injEq] at hu; rw [hu.2]; exact hY
  · intro h; exact Or.inr (Or.inr ⟨w', rfl, h⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (2) for the product: product neighbourhoods intersect componentwise. -/
theorem prodTokNbhd_inter (X X' Y Y' : Set Str) :
    prodTokNbhd X Y ∩ prodTokNbhd X' Y' = prodTokNbhd (X ∩ X') (Y ∩ Y') := by
  ext w
  cases w with
  | nil => simp [Set.mem_inter_iff]
  | cons b w' => cases b <;> simp [Set.mem_inter_iff]

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (1) for the product: inclusion of product neighbourhoods is componentwise. -/
theorem prodTokNbhd_subset_iff {X X' Y Y' : Set Str} :
    prodTokNbhd X Y ⊆ prodTokNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · exact mem_prodTokNbhd_false.mp (h (mem_prodTokNbhd_false.mpr ha))
    · exact mem_prodTokNbhd_true.mp (h (mem_prodTokNbhd_true.mpr hb))
  · rintro ⟨hX, hY⟩ w hw
    cases w with
    | nil => exact mem_prodTokNbhd_nil
    | cons b w' =>
      cases b with
      | false => exact mem_prodTokNbhd_false.mpr (hX (mem_prodTokNbhd_false.mp hw))
      | true => exact mem_prodTokNbhd_true.mpr (hY (mem_prodTokNbhd_true.mp hw))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.19 — the concrete product system `𝒟₀ × 𝒟₁` over `{0,1}*`.** Neighbourhoods are
`{Λ} ∪ 0X ∪ 1Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closed under consistent intersection by Scott's (1)/(2)
together with the factors' closure. -/
def prodTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodTokNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀, D₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem prodTokNbhd_injective {X X' Y Y' : Set Str} (h : prodTokNbhd X Y = prodTokNbhd X' Y') :
    X = X' ∧ Y = Y' :=
  ⟨Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).1
      (prodTokNbhd_subset_iff.mp h.symm.subset).1,
   Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).2
      (prodTokNbhd_subset_iff.mp h.symm.subset).2⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem prodTok_mem_iff {W : Set Str} :
    (prodTok D₀ D₁).mem W ↔ ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem prodTok_master : (prodTok D₀ D₁).master = prodTokNbhd D₀.master D₁.master := rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem prodTok_mem_prodTokNbhd {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y) :
    (prodTok D₀ D₁).mem (prodTokNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's `z₀`: the first component of a `prodTok`-element. -/
def fstTok (z : (prodTok D₀ D₁).Element) : D₀.Element where
  mem X := D₀.mem X ∧ z.mem (prodTokNbhd X D₁.master)
  sub h := h.1
  master_mem := ⟨D₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodTokNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (prodTok_mem_prodTokNbhd hX' D₁.master_mem)
      (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩)⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_fstTok {z : (prodTok D₀ D₁).Element} {X : Set Str} :
    (fstTok z).mem X ↔ D₀.mem X ∧ z.mem (prodTokNbhd X D₁.master) := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's `z₁`: the second component of a `prodTok`-element. -/
def sndTok (z : (prodTok D₀ D₁).Element) : D₁.Element where
  mem Y := D₁.mem Y ∧ z.mem (prodTokNbhd D₀.master Y)
  sub h := h.1
  master_mem := ⟨D₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodTokNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    exact ⟨hY', z.up_mem hzY (prodTok_mem_prodTokNbhd D₀.master_mem hY')
      (prodTokNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩)⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_sndTok {z : (prodTok D₀ D₁).Element} {Y : Set Str} :
    (sndTok z).mem Y ↔ D₁.mem Y ∧ z.mem (prodTokNbhd D₀.master Y) := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The element pairing `⟨x, y⟩` for the concrete product. -/
def pairTok (x : D₀.Element) (y : D₁.Element) : (prodTok D₀ D₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodTokNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prodTok_mem_prodTokNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨D₀.master, D₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodTokNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem mem_pairTok_prodTokNbhd {x : D₀.Element} {y : D₁.Element} {X Y : Set Str} :
    (pairTok x y).mem (prodTokNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fstTok_pairTok (x : D₀.Element) (y : D₁.Element) : fstTok (pairTok x y) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).1
  · intro hX; exact ⟨x.sub hX, mem_pairTok_prodTokNbhd.mpr ⟨hX, y.master_mem⟩⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (3) for the product: membership of `X ∪ Y` splits into its two slices. -/
theorem prodTok_mem_split {z : (prodTok D₀ D₁).Element} {X Y : Set Str}
    (hX : D₀.mem X) (hY : D₁.mem Y) :
    z.mem (prodTokNbhd X Y) ↔
      z.mem (prodTokNbhd X D₁.master) ∧ z.mem (prodTokNbhd D₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prodTok_mem_prodTokNbhd hX D₁.master_mem) ?_,
            z.up_mem h (prodTok_mem_prodTokNbhd D₀.master_mem hY) ?_⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨subset_rfl, D₁.sub_master hY⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodTokNbhd_inter, Set.inter_eq_left.mpr (D₀.sub_master hX),
      Set.inter_eq_right.mpr (D₁.sub_master hY)] at this

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem pairTok_fstTok_sndTok (z : (prodTok D₀ D₁).Element) : pairTok (fstTok z) (sndTok z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prodTok_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prodTok_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem sndTok_pairTok (x : D₀.Element) (y : D₁.Element) : sndTok (pairTok x y) = y := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).2
  · intro hY; exact ⟨y.sub hY, mem_pairTok_prodTokNbhd.mpr ⟨x.master_mem, hY⟩⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The order-isomorphism `|D₀ × D₁|ₜₒₖ ≃o |D₀| × |D₁|` (Scott's Proposition 3.2, token-level). -/
def prodTokEquiv : (prodTok D₀ D₁).Element ≃o D₀.Element × D₁.Element where
  toFun z := (fstTok z, sndTok z)
  invFun p := pairTok p.1 p.2
  left_inv z := pairTok_fstTok_sndTok z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prodTok_mem_split hX hY).mp hW
      have hX' : (fstTok z').mem X := h1 X ⟨hX, ha⟩
      have hY' : (sndTok z').mem Y := h2 Y ⟨hY, hb⟩
      exact (prodTok_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem toSum_fromSum (s : (sum D₀ D₁ h₀ h₁).Element) : toSum (fromSum s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromSum_mem_embF hX).mp hs
    · exact (fromSum_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromSum_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromSum_mem_embT hY).mpr hW⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.19 — the concrete sum is correct up to isomorphism.** The order-isomorphism
`|D₀ + D₁|ₜₒₖ ≃o |D₀ + D₁|` between Scott's `{0,1}*`-presentation and the abstract separated sum. -/
def sumTokEquiv : (sumTok D₀ D₁ h₀ h₁).Element ≃o (sum D₀ D₁ h₀ h₁).Element where
  toFun := toSum
  invFun := fromSum
  left_inv := fromSum_toSum
  right_inv := toSum_fromSum
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases x.sub hX with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toSum_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toSum_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- `prodTokNbhd D₀.master D₁.master` is exactly the sum master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
theorem prodTokNbhd_master_eq : prodTokNbhd D₀.master D₁.master = sumTokMaster D₀ D₁ := rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (product).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ × 𝒟₁` is isomorphic, as a domain, to the abstract product of Definition 3.1.
Both compute the same domain `|D₀| × |D₁|` (via `prodTokEquiv` and Scott's `prodEquiv`). -/
theorem prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁ :=
  ⟨prodTokEquiv.trans (prodEquiv D₀ D₁).symm⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- The concrete product is again `∅`-free (every neighbourhood contains `Λ`). -/
theorem prodTok_nonempty : ∀ W, (prodTok D₀ D₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, _, _, rfl⟩; exact ⟨[], mem_prodTokNbhd_nil⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (sum).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ + 𝒟₁` is isomorphic, as a domain, to the abstract separated sum of
Exercise 3.18. -/
theorem sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁ := ⟨sumTokEquiv⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_619 : And
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁))
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
    {h₀ :
      ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ X →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
    {h₁ :
      ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁ Y →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Option (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str))
      (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)
      (@DomainTheory.NeighbourhoodSystems.sum DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁ h₀ h₁)) :=
  @And.intro
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁))
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
    {h₀ :
      ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ X →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
    {h₁ :
      ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁ Y →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Option (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str))
      (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)
      (@DomainTheory.NeighbourhoodSystems.sum DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁ h₀ h₁))
  @DomainTheory.NeighbourhoodSystems.Exercise619.prodTok_iso_prod
  @DomainTheory.NeighbourhoodSystems.Exercise619.sumTok_iso_sum
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_master : (sumTok D₀ D₁ h₀ h₁).mem (sumTokMaster D₀ D₁) := Or.inl rfl

end Exercise619
end

section
open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- The concrete sum is again `∅`-free (an object of Scott's category). -/
theorem sumTok_nonempty : ∀ W, (sumTok D₀ D₁ h₀ h₁).mem W → W.Nonempty :=
  fun _ h => sumTok_mem_nonempty h

end Exercise619
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- A **product neighbourhood** `iprodNbhd X = {⟨i, a⟩ ∣ a ∈ X i}` over `Σ i, α i`. -/
def iprodNbhd (X : ∀ i, Set (α i)) : Set (Σ i, α i) := {p | p.2 ∈ X p.1}

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

@[simp] theorem mem_iprodNbhd {X : ∀ i, Set (α i)} {i : ι} {a : α i} :
    (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X ↔ a ∈ X i := Iff.rfl

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Choice-free finite support**: a *list* enumerating all coordinates where `X` is non-master.
(Mathlib's `Set.Finite` is built on `Fintype` and pulls in `Classical.choice`; a `List` witness keeps
the construction constructive, which is exactly what is needed for the cylinder.) -/
def FinSupp (D : ∀ i, NeighborhoodSystem (α i)) (X : ∀ i, Set (α i)) : Prop :=
  ∃ l : List ι, ∀ i, i ∉ l → X i = (D i).master

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem FinSupp.inter {X X' : ∀ i, Set (α i)}
    (hX : FinSupp D X) (hX' : FinSupp D X') : FinSupp D (fun i => X i ∩ X' i) := by
  obtain ⟨l, hl⟩ := hX; obtain ⟨l', hl'⟩ := hX'
  -- Outside `l ++ l'` both factors are the master, so the intersection is too — fully constructive,
  -- no case split on the undecidable proposition `X i = master`.
  refine ⟨l ++ l', fun i hi => ?_⟩
  rw [List.mem_append, not_or] at hi
  simp only [hl i hi.1, hl' i hi.2, Set.inter_self]

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- The tuple representation of a product neighbourhood is unique. -/
theorem iprodNbhd_injective {X X' : ∀ i, Set (α i)} (h : iprodNbhd X = iprodNbhd X') : X = X' := by
  funext i; apply Set.ext; intro a
  simpa only [mem_iprodNbhd] using Set.ext_iff.mp h ⟨i, a⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- Product neighbourhoods intersect coordinatewise (Scott's (2)). -/
theorem iprodNbhd_inter (X X' : ∀ i, Set (α i)) :
    iprodNbhd X ∩ iprodNbhd X' = iprodNbhd (fun i => X i ∩ X' i) := by
  apply Set.ext; rintro ⟨i, a⟩; simp [iprodNbhd, Set.mem_inter_iff]

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- Inclusion of product neighbourhoods is coordinatewise (Scott's (1)). -/
theorem iprodNbhd_subset_iff {X X' : ∀ i, Set (α i)} :
    iprodNbhd X ⊆ iprodNbhd X' ↔ ∀ i, X i ⊆ X' i := by
  constructor
  · intro h i a ha; exact h (show (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X from ha)
  · rintro h ⟨i, a⟩ ha; exact h i ha

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem FinSupp.master : FinSupp D (fun i => (D i).master) := ⟨[], fun _ _ => rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]

variable (D) in
/- concordance: source L4215 EXERCISE 6.29 infinitary sum and product -/
/-- **Exercise 6.29 — the indexed product `∏_i D_i`.** The index type is non-empty so the
dependent-sum token set contains a token. Neighbourhoods are cylinders: tuples `X i ∈ 𝒟ᵢ`
that are the master in all but finitely many coordinates. -/
def iprod : NeighborhoodSystem (Σ i, α i) where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := ⟨fun i => (D i).master, fun i => (D i).master_mem, FinSupp.master, rfl⟩
  sub_master := by
    rintro W ⟨X, hX, _, rfl⟩
    exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩ ⟨ZZ, hZZ, _, rfl⟩ hsub
    rw [iprodNbhd_inter] at hsub ⊢
    refine ⟨fun i => X i ∩ X' i, fun i => ?_, hXf.inter hX'f, rfl⟩
    have : ZZ i ⊆ X i ∩ X' i := iprodNbhd_subset_iff.mp hsub i
    exact (D i).inter_mem (hX i) (hX' i) (hZZ i) this

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]

section Iso

variable [DecidableEq ι]

/-- The tuple that is `U` at coordinate `i` and the master elsewhere. -/
def updTuple (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : ∀ j, Set (α j) :=
  Function.update (fun j => (D j).master) i U

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
@[simp] theorem updTuple_apply_self (i : ι) (U : Set (α i)) : updTuple D i U i = U := by
  simp [updTuple]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **The element of `∏_i D_i` assembled from a tuple of components.** -/
def fromPi (D : ∀ i, NeighborhoodSystem (α i)) (x : ∀ i, (D i).Element) : (iprod D).Element where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (x i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  sub := by rintro W ⟨X, hX, hXf, rfl⟩; exact ⟨X, fun i => (x i).sub (hX i), hXf, rfl⟩
  master_mem := ⟨fun i => (D i).master, fun i => (x i).master_mem, FinSupp.master, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩
    exact ⟨fun i => X i ∩ X' i, fun i => (x i).inter_mem (hX i) (hX' i), hXf.inter hX'f,
      iprodNbhd_inter X X'⟩
  up_mem := by
    rintro W W' ⟨X, hX, _, rfl⟩ hW' hsub
    obtain ⟨X', hX'mem, hX'f, rfl⟩ := hW'
    rw [iprodNbhd_subset_iff] at hsub
    exact ⟨X', fun i => (x i).up_mem (hX i) (hX'mem i) (hsub i), hX'f, rfl⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged copy `inj i X = {some ⟨i, a⟩ ∣ a ∈ X}` of summand `i`. -/
def injI (i : ι) (X : Set (α i)) : Set (Option (Σ i, α i)) :=
  (fun a => (some ⟨i, a⟩ : Option (Σ i, α i))) '' X

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem none_not_mem_injI {i : ι} {X : Set (α i)} : (none : Option (Σ i, α i)) ∉ injI i X := by
  rintro ⟨a, _, heq⟩; simp at heq

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- The cylinder restricted to a list of coordinates `l` (master outside `l`). -/
def restrictTo (D : ∀ i, NeighborhoodSystem (α i)) (l : List ι) (X : ∀ i, Set (α i)) :
    ∀ j, Set (α j) := fun j => if j ∈ l then X j else (D j).master

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- The slice cylinder: `U` at coordinate `i`, master elsewhere. -/
def slice (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : Set (Σ i, α i) :=
  iprodNbhd (updTuple D i U)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- Recovering the coordinate from a slice neighbourhood. -/
theorem iprod_mem_slice_inv {i : ι} {U : Set (α i)} (h : (iprod D).mem (slice D i U)) :
    (D i).mem U := by
  obtain ⟨X, hX, _, heq⟩ := h
  have hXeq : updTuple D i U = X := iprodNbhd_injective heq
  have hi := hX i
  rwa [← hXeq, updTuple_apply_self] at hi

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem slice_eq (i : ι) (U : Set (α i)) : slice D i U = iprodNbhd (updTuple D i U) := rfl

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

@[simp] theorem some_mem_injI {i : ι} {a : α i} {X : Set (α i)} :
    (some ⟨i, a⟩ : Option (Σ i, α i)) ∈ injI i X ↔ a ∈ X := by
  constructor
  · rintro ⟨b, hb, heq⟩
    simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
    rwa [heq] at hb
  · intro ha; exact ⟨a, ha, rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged token determines its summand index. -/
theorem index_of_some_mem_injI {i k : ι} {a : α k} {X : Set (α i)}
    (hmem : (some ⟨k, a⟩ : Option (Σ i, α i)) ∈ injI i X) : k = i := by
  obtain ⟨b, _, heq⟩ := hmem
  simp only [Option.some.injEq] at heq
  exact (congrArg Sigma.fst heq).symm

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_inter_same (i : ι) (X Y : Set (α i)) : injI i X ∩ injI i Y = injI i (X ∩ Y) := by
  apply Set.ext
  rintro (_ | ⟨k, a⟩)
  · constructor
    · rintro ⟨h, _⟩; exact absurd h none_not_mem_injI
    · intro h; exact absurd h none_not_mem_injI
  · constructor
    · rintro ⟨hx, hy⟩
      obtain rfl := index_of_some_mem_injI hx
      exact some_mem_injI.mpr ⟨some_mem_injI.mp hx, some_mem_injI.mp hy⟩
    · intro h
      obtain rfl := index_of_some_mem_injI h
      have h' := some_mem_injI.mp h
      exact ⟨some_mem_injI.mpr h'.1, some_mem_injI.mpr h'.2⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_iff {i : ι} {X Y : Set (α i)} : injI i X ⊆ injI i Y ↔ X ⊆ Y := by
  constructor
  · intro h a ha; exact some_mem_injI.mp (h (some_mem_injI.mpr ha))
  · intro h; rintro w ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed smash product `⊗_i D_i`.** The index type is non-empty so its
dependent-sum token set is non-empty. A proper neighbourhood is a cylinder proper in *every*
coordinate; closure under intersection is as for `iprod` plus the observation that
`X i ∩ X' i ⊆ X i ≠` master stays proper. -/
def iotimes [Nonempty ι] (D : ∀ i, NeighborhoodSystem (α i)) : NeighborhoodSystem (Σ i, α i) where
  mem W := W = iprodNbhd (fun i => (D i).master) ∨
    ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ (∀ i, X i ≠ (D i).master) ∧
      FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, _, _, rfl⟩)
    · exact subset_rfl
    · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨X, hX, hXne, hXf, rfl⟩
    · have hW'sub : W' ⊆ iprodNbhd (fun i => (D i).master) := by
        rcases hW' with rfl | ⟨X', hX', _, _, rfl⟩
        · exact subset_rfl
        · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX' i)
      rw [Set.inter_eq_right.mpr hW'sub]; exact hW'
    · rcases hW' with rfl | ⟨X', hX', hX'ne, hX'f, rfl⟩
      · rw [Set.inter_eq_left.mpr (iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i))]
        exact Or.inr ⟨X, hX, hXne, hXf, rfl⟩
      · rw [iprodNbhd_inter] at hsub ⊢
        obtain ⟨ZZ, hZZmem, rfl⟩ : ∃ ZZ, (∀ i, (D i).mem (ZZ i)) ∧ Z = iprodNbhd ZZ := by
          rcases hZ with rfl | ⟨ZZ, hZZ, _, _, rfl⟩
          · exact ⟨fun i => (D i).master, fun i => (D i).master_mem, rfl⟩
          · exact ⟨ZZ, hZZ, rfl⟩
        refine Or.inr ⟨fun i => X i ∩ X' i, fun i => ?_, fun i => ?_, ?_, rfl⟩
        · exact (D i).inter_mem (hX i) (hX' i) (hZZmem i) (iprodNbhd_subset_iff.mp hsub i)
        · intro heq
          exact hXne i (Set.Subset.antisymm ((D i).sub_master (hX i))
            (by rw [← heq]; exact Set.inter_subset_left))
        · exact hXf.inter hX'f

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- The basepoint master of the indexed sum: `{none} ∪ {some ⟨i, a⟩ ∣ a ∈ Δᵢ}`. -/
def sumMasterI (D : ∀ i, NeighborhoodSystem (α i)) : Set (Option (Σ i, α i)) :=
  insert none ((fun p => (some p : Option (Σ i, α i))) '' iprodNbhd (fun i => (D i).master))

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_sumMasterI {i : ι} {X : Set (α i)} (hX : (D i).mem X) :
    injI i X ⊆ sumMasterI D := by
  rintro w ⟨a, ha, rfl⟩
  exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨i, a⟩, (D i).sub_master hX ha, rfl⟩)

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem none_mem_sumMasterI : (none : Option (Σ i, α i)) ∈ sumMasterI D := Set.mem_insert _ _

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed coalesced sum `⊕_i D_i`.** -/
def ioplus (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ X ≠ (D i).master ∧ W = injI i X
  master := sumMasterI D
  master_nonempty := ⟨none, none_mem_sumMasterI⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, _, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, hXne, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, _, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, hYne, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, hXne, rfl⟩
      · rcases hZ with rfl | ⟨k, Wk, hWk, _, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub),
            fun heq => hXne (Set.Subset.antisymm ((D k).sub_master hX)
              (heq ▸ Set.inter_subset_left)), rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed separated sum `∑_i D_i`.** -/
def isum (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ W = injI i X
  master := sumMasterI D
  master_nonempty := ⟨none, none_mem_sumMasterI⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, rfl⟩
      · -- both proper: the consistency witness `Z` forces `i = j` constructively.
        rcases hZ with rfl | ⟨k, Wk, hWk, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub), rfl⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem updTuple_apply_ne {i j : ι} (U : Set (α i)) (h : j ≠ i) :
    updTuple D i U j = (D j).master := by
  simp [updTuple, Function.update_of_ne h]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem fromPi_mem_slice (x : ∀ i, (D i).Element) (i : ι) (U : Set (α i)) :
    (fromPi D x).mem (slice D i U) ↔ (x i).mem U := by
  constructor
  · rintro ⟨X, hX, _, heq⟩
    have hXeq : updTuple D i U = X := iprodNbhd_injective heq
    have hi := hX i
    rwa [← hXeq, updTuple_apply_self] at hi
  · intro hU
    refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
    · by_cases h : j = i
      · subst h; rw [updTuple_apply_self]; exact hU
      · rw [updTuple_apply_ne U h]; exact (x j).master_mem
    · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
theorem iprodNbhd_restrictTo_cons {X : ∀ i, Set (α i)} (hXsub : ∀ i, X i ⊆ (D i).master)
    (a : ι) (l : List ι) :
    iprodNbhd (restrictTo D (a :: l) X) = slice D a (X a) ∩ iprodNbhd (restrictTo D l X) := by
  rw [slice_eq, iprodNbhd_inter]
  congr 1; funext j
  show (if j ∈ a :: l then X j else (D j).master)
      = updTuple D a (X a) j ∩ (if j ∈ l then X j else (D j).master)
  by_cases hja : j = a
  · subst hja
    rw [updTuple_apply_self]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left List.mem_cons_self, ite_eq_left hjl, Set.inter_self]
    · rw [ite_eq_left List.mem_cons_self, ite_eq_right hjl, Set.inter_eq_left.mpr (hXsub j)]
  · rw [updTuple_apply_ne (X a) hja]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left (List.mem_cons_of_mem a hjl), ite_eq_left hjl, Set.inter_eq_right.mpr (hXsub j)]
    · rw [ite_eq_right fun h => (List.mem_cons.mp h).elim hja hjl, ite_eq_right hjl, Set.inter_self]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- A cylinder is contained in each of its own slices. -/
theorem iprodNbhd_subset_slice {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i)) (i : ι) :
    iprodNbhd X ⊆ slice D i (X i) := by
  rw [slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self]
  · rw [updTuple_apply_ne (X i) h]; exact (D j).sub_master (hX j)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- A slice has support `⊆ {i}`, hence is a neighbourhood of the product when `U ∈ 𝒟ᵢ`. -/
theorem iprod_mem_slice {i : ι} {U : Set (α i)} (hU : (D i).mem U) :
    (iprod D).mem (slice D i U) := by
  refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
  · by_cases h : j = i
    · subst h; rw [updTuple_apply_self]; exact hU
    · rw [updTuple_apply_ne U h]; exact (D j).master_mem
  · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- Slices at the same coordinate intersect by intersecting their data. -/
theorem slice_inter (i : ι) (U U' : Set (α i)) :
    slice D i U ∩ slice D i U' = slice D i (U ∩ U') := by
  rw [slice_eq, slice_eq, slice_eq, iprodNbhd_inter]
  congr 1; funext j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self, updTuple_apply_self]
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h, updTuple_apply_ne (U ∩ U') h,
      Set.inter_self]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- Slices are monotone in their data. -/
theorem slice_subset (i : ι) {U U' : Set (α i)} (hUU' : U ⊆ U') : slice D i U ⊆ slice D i U' := by
  rw [slice_eq, slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self]; exact hUU'
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h]

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **The `i`-th component of a product element** (Scott's `z_i`). -/
def proj (z : (iprod D).Element) (i : ι) : (D i).Element where
  mem U := (D i).mem U ∧ z.mem (slice D i U)
  sub h := h.1
  master_mem := ⟨(D i).master_mem, by
    have : slice D i (D i).master = (iprod D).master := by
      show iprodNbhd (updTuple D i (D i).master) = iprodNbhd (fun j => (D j).master)
      congr 1; funext j
      by_cases h : j = i
      · subst h; rw [updTuple_apply_self]
      · rw [updTuple_apply_ne (D i).master h]
    rw [this]; exact z.master_mem⟩
  inter_mem := by
    rintro U U' ⟨_, hzU⟩ ⟨_, hzU'⟩
    have hz := z.inter_mem hzU hzU'
    rw [slice_inter] at hz
    exact ⟨iprod_mem_slice_inv (z.sub hz), hz⟩
  up_mem := by
    rintro U U' ⟨_, hzU⟩ hU' hUU'
    exact ⟨hU', z.up_mem hzU (iprod_mem_slice hU') (slice_subset i hUU')⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem proj_fromPi (x : ∀ i, (D i).Element) (i : ι) : proj (fromPi D x) i = x i := by
  apply Element.ext
  intro U
  constructor
  · rintro ⟨_, hz⟩; exact (fromPi_mem_slice x i U).mp hz
  · intro hU; exact ⟨(x i).sub hU, (fromPi_mem_slice x i U).mpr hU⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- An element contains the restricted cylinder once it contains each listed slice. -/
theorem z_mem_iprodNbhd_restrictTo (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXsub : ∀ i, X i ⊆ (D i).master) (hslice : ∀ i, z.mem (slice D i (X i))) (l : List ι) :
    z.mem (iprodNbhd (restrictTo D l X)) := by
  induction l with
  | nil =>
    have : restrictTo D [] X = fun j => (D j).master := by
      funext j; rw [restrictTo]; exact ite_eq_right List.not_mem_nil
    rw [this]; exact z.master_mem
  | cons a l ih =>
    rw [iprodNbhd_restrictTo_cons hXsub a l]
    exact z.inter_mem (hslice a) ih

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **Reconstruction.** A product element containing each of a cylinder's slices contains the
cylinder. The finite support (a *list* of coordinates) lets the only finitely many non-trivial slices
be intersected inside the element — entirely choice-free. -/
theorem z_mem_of_slices (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXmem : ∀ i, (D i).mem (X i)) (hXf : FinSupp D X)
    (hslice : ∀ i, z.mem (slice D i (X i))) : z.mem (iprodNbhd X) := by
  obtain ⟨l, hl⟩ := hXf
  have hsub : ∀ i, X i ⊆ (D i).master := fun i => (D i).sub_master (hXmem i)
  have key := z_mem_iprodNbhd_restrictTo z hsub hslice l
  have heq : restrictTo D l X = X := by
    funext j
    rw [restrictTo]
    by_cases h : j ∈ l
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact (hl j h).symm
  rwa [heq] at key

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

theorem fromPi_toPi (z : (iprod D).Element) : fromPi D (fun i => proj z i) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hX, hXf, rfl⟩
    exact z_mem_of_slices z (fun i => (hX i).1) hXf (fun i => (hX i).2)
  · intro hW
    obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hW
    exact ⟨X, fun i => ⟨hXmem i, z.up_mem hW (iprod_mem_slice (hXmem i))
      (iprodNbhd_subset_slice hXmem i)⟩, hXf, rfl⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

/-- **Exercise 6.29 — `×` generalizes to `∏`, correct up to isomorphism.** The domain of the
indexed product is the pointwise product of the factor domains: `|∏_i D_i| ≃o ∀ i, |D_i|`. This is
the infinitary **Proposition 3.2** (`prodEquiv`). -/
def iprodEquiv (D : ∀ i, NeighborhoodSystem (α i)) :
    (iprod D).Element ≃o (∀ i, (D i).Element) where
  toFun z := fun i => proj z i
  invFun x := fromPi D x
  left_inv z := fromPi_toPi z
  right_inv x := funext fun i => proj_fromPi x i
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hzW
      obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hzW
      refine z_mem_of_slices z' hXmem hXf fun i => ?_
      have hzi : (proj z i).mem (X i) :=
        ⟨hXmem i, z.up_mem hzW (iprod_mem_slice (hXmem i)) (iprodNbhd_subset_slice hXmem i)⟩
      exact ((h i) (X i) hzi).2
    · intro h i U hU
      exact ⟨hU.1, h _ hU.2⟩

end Iso

end IndexedProduct

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


theorem injI_inter_ne {i j : ι} (h : i ≠ j) (X : Set (α i)) (Y : Set (α j)) :
    injI i X ∩ injI j Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro (_ | ⟨k, a⟩) ⟨hw1, hw2⟩
  · exact none_not_mem_injI hw1
  · exact h ((index_of_some_mem_injI hw1).symm.trans (index_of_some_mem_injI hw2))

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


theorem injI_nonempty {i : ι} {X : Set (α i)} (hX : X.Nonempty) : (injI i X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨some ⟨i, a⟩, some_mem_injI.mpr ha⟩

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — `⊗` does not generalize.** Over an infinite index, the smash product has only
its basepoint: an all-coordinates-proper cylinder has support `Set.univ`, which cannot be finite. -/
theorem iotimes_only_master [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    ∀ W, (iotimes D).mem W → W = (iotimes D).master := by
  rintro W (rfl | ⟨X, _, hXne, ⟨l, hl⟩, rfl⟩)
  · rfl
  · -- Every coordinate is proper, so the finite support list `l` would have to contain *all* of `ι`,
    -- impossible for an infinite index. This is a cardinality argument: Prop-level and unavoidably
    -- classical (Mathlib's `Set.Finite`/`Fintype` API is built on `Classical.choice`).
    refine absurd ((List.finite_toSet l).subset (fun i _ => ?_)) Set.infinite_univ
    exact not_not.mp fun hni => hXne i (hl i hni)

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — the infinite smash collapses to one point.** Its element domain is a
singleton (`⊥` only), so `⊗` has no sensible infinitary generalization. -/
theorem iotimes_subsingleton [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    Subsingleton (iotimes D).Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro W
  constructor
  · intro hx; rw [iotimes_only_master D W (x.sub hx)]; exact y.master_mem
  · intro hy; rw [iotimes_only_master D W (y.sub hy)]; exact x.master_mem

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


section IndexedProduct

variable [Nonempty ι]


theorem iprod_mem_iprodNbhd {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i))
    (hXf : FinSupp D X) : (iprod D).mem (iprodNbhd X) :=
  ⟨X, hX, hXf, rfl⟩

end IndexedProduct
end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — a sum element reaches at most one summand.** -/
theorem isum_summand_unique {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) {i j : ι} {X : Set (α i)} {Y : Set (α j)}
    (hX : z.mem (injI i X)) (hY : z.mem (injI j Y)) : i = j := by
  -- The filter element `z` contains the consistent intersection; its representative carries a
  -- token whose index is forced to be both `i` and `j` — no excluded middle on `i = j`.
  have hz := z.inter_mem hX hY
  rcases z.sub hz with h0 | ⟨k, W, hWmem, hWeq⟩
  · rw [Set.ext_iff] at h0
    exact absurd ((h0 none).mpr none_mem_sumMasterI).1 none_not_mem_injI
  · obtain ⟨w, hw⟩ := hne k W hWmem
    rw [Set.ext_iff] at hWeq
    have hmem := (hWeq (some ⟨k, w⟩)).mpr (some_mem_injI.mpr hw)
    obtain rfl := index_of_some_mem_injI hmem.1
    obtain rfl := index_of_some_mem_injI hmem.2
    rfl

end Exercise629
end

section
open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — sum trichotomy.** Every element of `∑_i D_i` either reaches into some summand
or is the basepoint `⊥`. (Prop-level and genuinely classical: the case split is excluded middle on
whether `z` reaches a summand, so this depends on `Classical.choice`.) -/
theorem isum_trichotomy {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) :
    (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
      (∀ W, z.mem W → W = (isum D hne).master) := by
  by_cases h : ∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)
  · exact Or.inl h
  · refine Or.inr fun W hW => ?_
    rcases z.sub hW with rfl | ⟨i, X, hX, rfl⟩
    · rfl
    · exact absurd ⟨i, X, hX, hW⟩ h

end Exercise629
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise629
section
set_option linter.unusedVariables false

theorem example_629.{u, v} : And
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)))) :=
  @And.intro
  (And
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j))
  (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
    {hne :
      ∀ (i : ι) (X : Set (α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
    (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
        (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne)),
    Or
      (∃ (i : ι) (X : Set (α i)),
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X)))
      (∀ (W : Set (Option (@Sigma ι fun (i : ι) => α i))),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z W →
          @Eq (Set (Option (@Sigma ι fun (i : ι) => α i))) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (Option (@Sigma ι fun (i : ι) => α i))
              (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))))
  (@And.intro
    (And
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D))))
    (∀ {ι : Type u} {α : ι → Type v} {D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)}
      {hne :
        ∀ (i : ι) (X : Set (α i)),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (α i) (D i) X → @Set.Nonempty (α i) X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne))
      {i j : ι} {X : Set (α i)} {Y : Set (α j)},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
          (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
          (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α i X) →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem (Option (@Sigma ι fun (i : ι) => α i))
            (@DomainTheory.NeighbourhoodSystems.Exercise629.isum ι α D hne) z
            (@DomainTheory.NeighbourhoodSystems.Exercise629.injI ι α j Y) →
          @Eq ι i j)
    (@And.intro
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i))
        (W : Set (@Sigma ι fun (i : ι) => α i)),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)
            W →
          @Eq (Set (@Sigma ι fun (i : ι) => α i)) W
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master (@Sigma ι fun (i : ι) => α i)
              (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
                (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      (∀ {ι : Type u} {α : ι → Type v} [inst : Infinite ι]
        (D : (i : ι) → DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (α i)),
        Subsingleton
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (@Sigma ι fun (i : ι) => α i)
            (@DomainTheory.NeighbourhoodSystems.Exercise629.iotimes ι α
              (@Nontrivial.to_nonempty ι (@Infinite.instNontrivial ι inst)) D)))
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_only_master
      @DomainTheory.NeighbourhoodSystems.Exercise629.iotimes_subsingleton)
    @DomainTheory.NeighbourhoodSystems.Exercise629.isum_summand_unique)
  @DomainTheory.NeighbourhoodSystems.Exercise629.isum_trichotomy
end

end DomainTheory.NeighbourhoodSystems.Exercise629
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Scott's `⊴` (the prose before Lemma 6.15).** `D ⊴ E` means `D ≅ D'` for some subdomain
`D' ◁ E`: `D` *embeds as a subdomain* of `E`. -/
def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The generator predicate: `Y` generates `i(↑X)`. Relationally, `X i Y` and `Y j X`. -/
def IsGen (X : Set α) (Y : Set β) : Prop := i.rel X Y ∧ j.rel Y X

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Generators exist** (uses `j ∘ i = I_D`). Every `D`-neighbourhood `X` has a generator: apply
`j ∘ i = I_D` to the identity relation `X I_D X`. -/
theorem isGen_exists (hji : j.comp i = idMap D) {X : Set α} (hX : D.mem X) :
    ∃ Y, IsGen i j X Y := by
  have hrel : (j.comp i).rel X X := by rw [hji]; exact ⟨hX, hX, subset_rfl⟩
  obtain ⟨Y, hiXY, hjYX⟩ := hrel
  exact ⟨Y, hiXY, hjYX⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Generators are closed under intersection.** If `Y, Y'` generate `X, X'` and `Y ∩ Y' ∈ E`, then
`Y ∩ Y'` generates `X ∩ X'`. Needs only `mono`/`inter_right` of `i` and `j` (the hypothesis
`E.mem (Y ∩ Y')` is what licenses the `j.mono` steps). -/
theorem isGen_inter {X X' : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y') (hE : E.mem (Y ∩ Y')) :
    IsGen i j (X ∩ X') (Y ∩ Y') := by
  obtain ⟨hiXY, hjYX⟩ := h
  obtain ⟨hiX'Y', hjY'X'⟩ := h'
  have hj1 : j.rel (Y ∩ Y') X :=
    j.mono hjYX Set.inter_subset_left subset_rfl hE (j.rel_cod hjYX)
  have hj2 : j.rel (Y ∩ Y') X' :=
    j.mono hjY'X' Set.inter_subset_right subset_rfl hE (j.rel_cod hjY'X')
  have hjInter : j.rel (Y ∩ Y') (X ∩ X') := j.inter_right hj1 hj2
  have hDXX' : D.mem (X ∩ X') := j.rel_cod hjInter
  have hi1 : i.rel (X ∩ X') Y :=
    i.mono hiXY Set.inter_subset_left subset_rfl hDXX' (i.rel_cod hiXY)
  have hi2 : i.rel (X ∩ X') Y' :=
    i.mono hiX'Y' Set.inter_subset_right subset_rfl hDXX' (i.rel_cod hiX'Y')
  exact ⟨i.inter_right hi1 hi2, hjInter⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The masters generate each other: `IsGen Δ_D Δ_E` (from `i.master_rel`, `j.master_rel`). -/
theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The image subdomain `D'`.** A `β`-set `Y` is a neighbourhood iff it generates some
`D`-neighbourhood; the master is `E`'s master. `isGen_inter` supplies condition (ii). -/
def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone** (uses `j ∘ i = I_D`): if `Y, Y'` generate `X, X'`
and `Y ⊆ Y'`, then `X ⊆ X'`. (Widen `X i Y` to `X i Y'` by `mono`, compose with `Y' j X'`, and read
off `X ⊆ X'` from `j ∘ i = I_D`.) -/
theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- Generators are unique in the first argument (`isGen_mono` both ways). -/
theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The generator correspondence is monotone, other direction** (uses `i ∘ j ⊆ I_E`): if `Z, W`
generate `X, X'` and `X ⊆ X'`, then `Z ⊆ W`. (Widen `Z j X` to `Z j X'` by `mono`, compose with
`X' i W`, and read off `Z ⊆ W` from `i ∘ j ⊆ I_E`.) -/
theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- Generators are unique in the second argument (`isGen_mono'` both ways). -/
theorem isGen_snd_unique (hij : i.comp j ≤ idMap E) {X : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X Y') : Y = Y' :=
  Set.Subset.antisymm (isGen_mono' i j hij h h' subset_rfl)
    (isGen_mono' i j hij h' h subset_rfl)

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **`D' ◁ E`.** Same master (`rfl`); `D' ⊆ E` since a generator's `Y` is an `E`-neighbourhood; and
the consistency clause `inter_closed` is exactly `isGen_inter`. -/
theorem Dprime_subsystem : Dprime i j ◁ E where
  master_eq := rfl
  sub := by rintro Y ⟨X, hg⟩; exact i.rel_cod hg.1
  inter_closed := by
    rintro Y₁ Y₂ ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ hE
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hE⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Inverse map of the isomorphism `D ≅ D'`.** `y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`. (Needs both
laws: `j ∘ i = I_D` for generator existence and `i ∘ j ⊆ I_E` for `isGen_mono'`.) -/
def ofEl (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E)
    (y : (Dprime i j).Element) : D.Element where
  mem X := ∃ Y, y.mem Y ∧ IsGen i j X Y
  sub := by rintro X ⟨Y, _, hg⟩; exact i.rel_dom hg.1
  master_mem := ⟨E.master, y.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁y, hg₁⟩ ⟨Y₂, hY₂y, hg₂⟩
    have hyInter : y.mem (Y₁ ∩ Y₂) := y.inter_mem hY₁y hY₂y
    have hEInter : E.mem (Y₁ ∩ Y₂) := (Dprime_subsystem i j).sub (y.sub hyInter)
    exact ⟨Y₁ ∩ Y₂, hyInter, isGen_inter i j hg₁ hg₂ hEInter⟩
  up_mem := by
    rintro X X' ⟨Y, hYy, hg⟩ hDX' hXX'
    obtain ⟨Y', hg'⟩ := isGen_exists i j hji hDX'
    have hYY' : Y ⊆ Y' := isGen_mono' i j hij hg hg' hXX'
    exact ⟨Y', y.up_mem hYy ⟨X', hg'⟩ hYY', hg'⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **Forward map of the isomorphism `D ≅ D'`.** `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` — the
generators of the members of `x`. (Needs `j ∘ i = I_D` for upward closure, via `isGen_mono`.) -/
def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The domain isomorphism `D ≅ D'`** (Scott's "inclusion-preserving one-one correspondence").
Built from `toEl`/`ofEl`; the inverse laws and order-reflection come from generator uniqueness. -/
def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

end ProjectionPair
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/- concordance: source L3827 PROPOSITION 6.12 projection pair -/
/-- **Proposition 6.12 + Lemma 6.15 packaged.** A subdomain relation `D ◁ E` is in particular a
witness of `D ⊴ E` (take `D' = D`). Together with `trianglelefteq_of_projectionPair`, this shows
`D ⊴ E` holds **iff** there is a projection pair `D ⇄ E`. -/
theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)


/- concordance: source L3957 LEMMA 6.15 subdomains from projection pairs -/
/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E → D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair
end

section
set_option linter.unusedVariables false

theorem theorem_615.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (i : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E)
  (j : @DomainTheory.NeighbourhoodSystems.ApproximableMap β α E D),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D E D j i)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap β β E E)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β E D E i j)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β E) →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_of_projectionPair
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

/-- The subsystems of `E`, ordered by the **subdomain relation** `◁`, form a partial order
(reflexive, transitive, antisymmetric — Definition 6.10's API). -/
instance subPartialOrder (E : NeighborhoodSystem α) :
    PartialOrder {D : NeighborhoodSystem α // D ◁ E} where
  le D₀ D₁ := D₀.1 ◁ D₁.1
  le_refl D := Subsystem.refl D.1
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := Subtype.ext (h₁.antisymm h₂)
end

end DomainTheory.NeighbourhoodSystems.Proposition611
namespace DomainTheory.NeighbourhoodSystems
namespace Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}
variable {D E : NeighborhoodSystem α}

/-- **A projection pair (Definition 6.13 vocabulary).** Bundles Scott's `i, j` together with the two
laws, ready for reuse in monotone/continuous-on-domains functors and the existence Theorem 6.14. -/
structure ProjectionPair (D E : NeighborhoodSystem α) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E
end

end Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The injection `i : D → E` of Proposition 6.12.** As a neighbourhood relation,
`X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y`. Element-wise (see `toElementMap_inj`) it is Scott's
`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
def inj (h : D ◁ E) : ApproximableMap D E where
  rel X Y := D.mem X ∧ E.mem Y ∧ X ⊆ Y
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨D.master_mem, E.master_mem, h.master_eq.subset⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, E.inter_mem hY hY' (h.sub hX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The projection `j : E → D` of Proposition 6.12.** As a neighbourhood relation,
`Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X`. Element-wise (see `toElementMap_proj`) it is Scott's
`j(y) = y ∩ D`. The `inter_right` law is exactly where Definition 6.10's consistency clause
(`inter_closed`) is used. -/
def proj (h : D ◁ E) : ApproximableMap E D where
  rel Y X := E.mem Y ∧ D.mem X ∧ Y ⊆ X
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨E.master_mem, D.master_mem, h.master_eq.symm.subset⟩
  inter_right := by
    rintro Y X X' ⟨hY, hX, hYX⟩ ⟨_, hX', hYX'⟩
    have hEinter : E.mem (X ∩ X') :=
      E.inter_mem (h.sub hX) (h.sub hX') hY (Set.subset_inter hYX hYX')
    exact ⟨hY, h.inter_closed hX hX' hEinter, Set.subset_inter hYX hYX'⟩
  mono := by
    rintro Y Y' X X' ⟨_, _, hYX⟩ hY'Y hXX' hY' hX'
    exact ⟨hY', hX', (hY'Y.trans hYX).trans hXX'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12, second law: `i ∘ j ⊆ I_E`.** A round trip `Y ⊆ X ⊆ Y'` through a common
`D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`. The reverse inclusion fails (not every
consistent `E`-pair factors through `D`), so this is an inclusion of relations, not an equality. -/
theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12, first law: `j ∘ i = I_D`.** Each side relates `X` and `Z` exactly when
`X, Z ∈ D` and `X ⊆ Z`: a round trip `X ⊆ Y ⊆ Z` through an `E`-neighbourhood `Y` collapses to
`X ⊆ Z` (forward), and `X ⊆ Z` factors through `Y = Z` (backward). Proved relationally, so
**choice-free**. -/
theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem
section
set_option linter.unusedVariables false

theorem theorem_612.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D)) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D))
  @DomainTheory.NeighbourhoodSystems.Subsystem.inj_comp_proj_le
  @DomainTheory.NeighbourhoodSystems.Subsystem.proj_comp_inj
end

end DomainTheory.NeighbourhoodSystems.Subsystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Subsystem

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{x ∈ |𝒟| ∣ g(x) ⊑ y}` of the first formula. By the Galois connection it is the
down-set `{x ∣ x ⊑ h(y)}` of `h(y)`. -/
def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

@[simp] theorem mem_lowerSet (P : ProjectionPair D E) {y : E.Element} {x : D.Element} :
    x ∈ P.lowerSet y ↔ P.inj.toElementMap x ≤ y := Iff.rfl

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{y ∈ |ℰ| ∣ x ⊑ h(y)}` of the second formula. By the Galois connection it is the
up-set `{y ∣ g(x) ⊑ y}` of `g(x)`. -/
def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/- concordance: source L4175 EXERCISE 6.25 projection pair laws -/
/-- **Exercise 6.25 — `g` maps consistent sets to consistent sets.** "Consistent" for sets of
elements is "bounded" (Exercise 1.27). If `S` is bounded by `b`, its image `{g(s) ∣ s ∈ S}` is
bounded by `g(b)` (monotonicity). -/
theorem inj_bounded (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    E.Bounded (P.inj.toElementMap '' S) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨P.inj.toElementMap b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact P.inj.toElementMap_mono (hb s hs)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`g(h(y)) ⊑ y`.** The second projection-pair law `g ∘ h ⊆ I_ℰ`, read on elements. -/
theorem inj_proj_apply_le (P : ProjectionPair D E) (y : E.Element) :
    P.inj.toElementMap (P.proj.toElementMap y) ≤ y := by
  have h := (le_iff_toElementMap_le.mp P.inj_comp_proj_le) y
  rwa [toElementMap_comp, toElementMap_idMap] at h

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`h(g(x)) = x`.** The first projection-pair law `h ∘ g = I_𝒟`, read on elements. -/
theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **Exercise 6.25, the Galois connection.** For `x ∈ |𝒟|`, `y ∈ |ℰ|`:
`g(x) ⊑ y ↔ x ⊑ h(y)`. So `g` (lower adjoint) and `h` (upper adjoint) determine each other.

`→`: apply the monotone `h` to `g(x) ⊑ y` and use `h(g(x)) = x`.
`←`: apply the monotone `g` to `x ⊑ h(y)` and use `g(h(y)) ⊑ y`. -/
theorem galois (P : ProjectionPair D E) (x : D.Element) (y : E.Element) :
    P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y := by
  constructor
  · intro hxy
    have := P.proj.toElementMap_mono hxy
    rwa [P.proj_inj_apply x] at this
  · intro hxy
    exact (P.inj.toElementMap_mono hxy).trans (P.inj_proj_apply_le y)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — `g` preserves `⊔` (not just *directed* unions).** For any bounded set `S`,
`g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`. This is the characteristic property of a lower adjoint.

* `⊒`: `g(⊔S)` is an upper bound of `{g(s)}` since `s ⊑ ⊔S` and `g` is monotone.
* `⊑`: by the Galois connection it suffices that `⊔S ⊑ h(⊔{g(s)})`, i.e. that each `s ⊑ h(⊔{g(s)})`;
  by the Galois connection again this is `g(s) ⊑ ⊔{g(s)}`, true by `le_sSup`. -/
theorem inj_sSup (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    P.inj.toElementMap (D.sSup S hS) =
      E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS) := by
  apply le_antisymm
  · refine (P.galois _ _).mpr (D.sSup_le S hS fun s hs => ?_)
    refine (P.galois s _).mp ?_
    exact E.le_sSup _ (P.inj_bounded hS) ⟨s, hs, rfl⟩
  · refine E.sSup_le _ (P.inj_bounded hS) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact P.inj.toElementMap_mono (D.le_sSup S hS hs)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- The set `{x ∣ g(x) ⊑ y}` is bounded: `h(y)` is an upper bound (it is in fact the top). -/
theorem lowerSet_bounded (P : ProjectionPair D E) (y : E.Element) :
    D.Bounded (P.lowerSet y) :=
  ⟨P.proj.toElementMap y, fun _ hx => (P.galois _ y).mp hx⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — "check that the set on the right is directed".** Any two members of
`{x ∣ g(x) ⊑ y}` have a common upper bound *inside the set*, namely `h(y)` itself (the down-set of
`h(y)` has `h(y)` as a top, so it is trivially directed). -/
theorem lowerSet_directed (P : ProjectionPair D E) (y : E.Element) :
    ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y,
      ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c := by
  intro a ha b hb
  exact ⟨P.proj.toElementMap y, P.inj_proj_apply_le y,
    (P.galois a y).mp ha, (P.galois b y).mp hb⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25, first extremal formula.** `h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`.

`h(y)` is the *greatest* member of the set (`g(h(y)) ⊑ y`, so `h(y)` is in it; every member is
`⊑ h(y)` by the Galois connection), hence it is the least upper bound. -/
theorem proj_eq_sSup (P : ProjectionPair D E) (y : E.Element) :
    P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y) := by
  apply le_antisymm
  · exact D.le_sSup _ (P.lowerSet_bounded y) (P.inj_proj_apply_le y)
  · exact D.sSup_le _ (P.lowerSet_bounded y) fun x hx => (P.galois x y).mp hx

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — "check that the set on the right is non-empty".** `g(x)` itself lies in
`{y ∣ x ⊑ h(y)}`, since `x ⊑ h(g(x)) = x`. -/
theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25, second extremal formula.** `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`.

`g(x)` is the *least* member of the set (`x ⊑ h(g(x)) = x`, so `g(x)` is in it; every member is
`⊒ g(x)` by the Galois connection), hence it is the greatest lower bound. -/
theorem inj_eq_sInf (P : ProjectionPair D E) (x : D.Element) :
    P.inj.toElementMap x = E.sInf (P.upperSet x) (P.upperSet_nonempty x) := by
  apply le_antisymm
  · exact E.le_sInf _ (P.upperSet_nonempty x) _ fun y hy => (P.galois x y).mpr hy
  · refine E.sInf_le _ (P.upperSet_nonempty x) ?_
    rw [mem_upperSet, P.proj_inj_apply x]

end Subsystem.ProjectionPair
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair
section
set_option linter.unusedVariables false

theorem example_625.{u_1} : And
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x))
  (@And.intro
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y)))
    (@And.intro
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c)))
      (@And.intro
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS)))
        (@And.intro
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x)))
          (@And.intro
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S))
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.galois
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded)
          @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_eq_sInf)
        @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_sSup)
      @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_directed)
    @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj_eq_sSup)
  @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty
end

end DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **A neighbourhood system is *finite*** when it has only finitely many neighbourhoods. -/
def NeighborhoodSystem.IsFinite {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  Finite {X : Set α // D.mem X}
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **The element-wise map of an injection `i` is an order embedding.** Given approximable maps
`i : D → E`, `j : E → D` with `j ∘ i = I_D`, the map `x ↦ i(x)` on elements is an order embedding
`|D| ↪o |E|`: monotone by `toElementMap_mono`, and order-reflecting because `j(·)` is a monotone
left inverse (`j(i(x)) = x`). Choice-free. -/
def projElementEmbedding {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D) (hji : j.comp i = idMap D) :
    D.Element ↪o E.Element :=
  OrderEmbedding.ofMapLEIff i.toElementMap (by
    have hround : ∀ x : D.Element, j.toElementMap (i.toElementMap x) = x := by
      intro x; rw [← toElementMap_comp, hji, toElementMap_idMap]
    intro a b
    constructor
    · intro h
      have hjm := toElementMap_mono j h
      rwa [hround a, hround b] at hjm
    · intro h
      exact toElementMap_mono i h)
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **`D ⊴ E` yields an order embedding `|D| ↪o |E|`.** Unfold `⊴` to an iso `|D| ≅o |D'|` onto a
subdomain `D' ◁ E`, turn `D' ◁ E` into Proposition 6.12's projection pair, and compose its
injection embedding with the iso. Choice-free. -/
theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **A finite system has a finite element domain.** A filter `x : |D|` is determined by which of
the (finitely many) neighbourhoods it contains, so `x ↦ {p | x.mem p.1}` injects `|D|` into the
finite powerset `Set {X // D.mem X}`. -/
theorem finite_element_of_isFinite {α : Type*} {D : NeighborhoodSystem α} (h : D.IsFinite) :
    Finite D.Element := by
  have : Finite {X : Set α // D.mem X} := h
  apply Finite.of_injective
    (β := Set {X : Set α // D.mem X}) (fun x => {p | x.mem p.1})
  intro x y hxy
  apply Element.ext
  intro X
  by_cases hX : D.mem X
  · have := Set.ext_iff.mp hxy ⟨X, hX⟩
    simpa using this
  · exact ⟨fun hmem => absurd (x.sub hmem) hX, fun hmem => absurd (y.sub hmem) hX⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Finite Cantor–Schröder–Bernstein (order version).** Mutual order embeddings between two
*finite* ordered types yield an order isomorphism. The embeddings are injective, so equal finite
cardinality forces `f` to be surjective; a surjective strictly-monotone map is an order iso. Uses
`Classical.choice` (via `Fintype`/surjection-section). -/
theorem orderIso_of_embeddings {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (f : P ↪o Q) (g : Q ↪o P) : Nonempty (P ≃o Q) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype P
  obtain ⟨_⟩ := nonempty_fintype Q
  have hcard : Fintype.card P = Fintype.card Q :=
    le_antisymm (Fintype.card_le_of_injective f f.injective)
      (Fintype.card_le_of_injective g g.injective)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, hcard⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := f.map_rel_iff' }⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/- concordance: source L4207 EXERCISE 6.28 finite embeddings cancel -/
/-- **Exercise 6.28 (core).** If `|D|` and `|E|` are finite and `D ⊴ E ⊴ D`, then `D ≅ᴰ E`.
The two `⊴`s give mutual order embeddings of the (finite) element domains, and
`orderIso_of_embeddings` upgrades them to an isomorphism. -/
theorem isomorphic_of_trianglelefteq_both [Finite D.Element] [Finite E.Element]
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  obtain ⟨f⟩ := h₁.elementEmbedding
  obtain ⟨g⟩ := h₂.elementEmbedding
  exact orderIso_of_embeddings f g
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Exercise 6.28 (Scott 1981, PRG-19; suggested by G. Plotkin).** If `𝒟` and `ℰ` are *finite*
neighbourhood systems with `𝒟 ⊴ ℰ` and `ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. -/
theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  have := finite_element_of_isFinite hD
  have := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂
end

section
set_option linter.unusedVariables false

theorem example_628.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_finite_system
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_trianglelefteq_both
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12 (Scott 1981, PRG-19).** Every subdomain relation `D ◁ E` gives rise to a
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. -/
def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}


/-- **Element-wise description of `i` (Scott's equation).** `i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}


/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`. -/
theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

end Subsystem
end

section
export CategoryTheory (Category)

open scoped CategoryTheory

universe u

abbrev compAfter {Obj : Type u} [Category.{v} Obj] {X Y Z : Obj} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
  f ≫ g
end

section
export CategoryTheory (Category)

open scoped CategoryTheory


scoped infixr:80 " ⊚ " => compAfter
end

section
export CategoryTheory (Category)
end

end DomainTheory.NeighbourhoodSystems
end

section
-- Endofunctor.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

/- concordance: source L3625 DEFINITION 6.3 functor -/
/-- **Definition 6.3 (Scott 1981, PRG-19).** A *functor* on a category into itself (an
*endofunctor*): an assignment `obj` on objects and `map` on morphisms preserving identities
(`map_id`) and composition (`map_comp`). -/
structure Endofunctor (Obj : Type u) [Category Obj] where
  /-- The action on objects. -/
  obj : Obj → Obj
  /-- The action on morphisms. -/
  map : {X Y : Obj} → (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  /-- `T(I_X) = I_{T(X)}`. -/
  map_id : ∀ (X : Obj), map ((𝟙 X)) = (𝟙 (obj X))
  /-- `T(g ∘ f) = T(g) ∘ T(f)`. -/
  map_comp : ∀ {X Y Z : Obj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)),
    map (g ⊚ f) = (map g) ⊚ (map f)

end DomainTheory.NeighbourhoodSystems
end

section
-- Iso.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- An isomorphism in the category: a pair of mutually inverse morphisms. -/
structure Iso (X Y : Obj) where
  /-- The forward morphism. -/
  hom : (X ⟶ Y)
  /-- The inverse morphism. -/
  inv : (Y ⟶ X)
  /-- `inv ∘ hom = I_X`. -/
  hom_inv_id : inv ⊚ hom = (𝟙 X)
  /-- `hom ∘ inv = I_Y`. -/
  inv_hom_id : hom ⊚ inv = (𝟙 Y)

end DomainTheory.NeighbourhoodSystems
end

section
-- TAlgebra.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

/- concordance: source L3667 DEFINITION 6.4 algebra for a functor -/
/-- **Definition 6.4 (Scott 1981, PRG-19).** A *`T`-algebra*: a domain `carrier` together with a
structure map `str : T(carrier) → carrier`. -/
structure TAlgebra (T : Endofunctor Obj) where
  /-- The underlying object `E`. -/
  carrier : Obj
  /-- The structure map `k : T(E) → E`. -/
  str : ((T.obj carrier) ⟶ carrier)

end DomainTheory.NeighbourhoodSystems
end

section
-- AlgHom.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *homomorphism* of `T`-algebras `(E,k) → (F,m)`: a map
`hom : E → F` making the square commute, i.e. `hom ∘ k = m ∘ T(hom)`. -/
structure AlgHom (A B : TAlgebra T) where
  /-- The underlying morphism `h : E → F`. -/
  hom : (A.carrier ⟶ B.carrier)
  /-- The homomorphism square `h ∘ k = m ∘ T(h)`. -/
  comm : hom ⊚ A.str = B.str ⊚ T.map hom

end DomainTheory.NeighbourhoodSystems
end

section
-- IsInitial.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

/- concordance: source L3705 DEFINITION 6.5 initial algebra -/
/-- **Definition 6.5 (Scott 1981, PRG-19).** A `T`-algebra `A` is *initial* iff there is a (unique)
homomorphism from `A` into every `T`-algebra. We package the homomorphism as the data `desc` and its
uniqueness as `uniq`. -/
structure IsInitial (A : TAlgebra T) where
  /-- The chosen homomorphism into any algebra `B`. -/
  desc : (B : TAlgebra T) → AlgHom A B
  /-- It is the only homomorphism `A → B`. -/
  uniq : ∀ (B : TAlgebra T) (h : AlgHom A B), h = desc B

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
/-- **The category of domains and approximable maps** (Scott's prose preceding Definition 6.3):
identities and associative composition come from Theorem 2.5 (`idMap_comp`, `comp_idMap`,
`comp_assoc`). -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := ApproximableMap.idMap D.sys
  comp f g := g.comp f
  id_comp f := ApproximableMap.comp_idMap f
  comp_id f := ApproximableMap.idMap_comp f
  assoc f g h := (ApproximableMap.comp_assoc h g f).symm
end

section
universe u
variable {Obj : Type u} [Category Obj]
variable {T : Endofunctor Obj}

namespace AlgHom

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    have hα := α.comm
    have hβ := β.comm
    have hmap := T.map_comp β.hom α.hom
    dsimp only [compAfter] at hα hβ hmap ⊢
    rw [← CategoryTheory.Category.assoc, hα, CategoryTheory.Category.assoc, hβ,
      ← CategoryTheory.Category.assoc, hmap]

end AlgHom
end

section
universe u
variable {Obj : Type u} [Category Obj]
variable {T : Endofunctor Obj}

namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := (𝟙 A.carrier)
  comm := by
    simp only [compAfter]
    rw [CategoryTheory.Category.comp_id, T.map_id, CategoryTheory.Category.id_comp]

end AlgHom
end

section
universe u
variable {Obj : Type u} [Category Obj]
variable {T : Endofunctor Obj}

namespace AlgHom


@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = (𝟙 A.carrier) := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom
end

section
universe u

/-- The **identity endofunctor** on any category: it fixes objects and morphisms. (A convenient
witness that `Endofunctor` is inhabited; used to show Definition 6.8 is non-vacuous.) -/
def idEndofunctor (Obj : Type u) [Category Obj] : Endofunctor Obj where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
end

section
universe u

@[simp] theorem idEndofunctor_obj {Obj : Type u} [Category Obj] (X : Obj) :
    (idEndofunctor Obj).obj X = X := rfl
end

section
universe u

@[simp] theorem idEndofunctor_map {Obj : Type u} [Category Obj] {X Y : Obj}
    (f : (X ⟶ Y)) : (idEndofunctor Obj).map f = f := rfl
end

section
/- concordance: source L3765 DEFINITION 6.8 continuity on maps -/
/-- **Definition 6.8 (Scott 1981, PRG-19).** An endofunctor `T` on the category of domains is
*continuous on maps* when, for every pair of domains `D` and `E`, the induced action `λf. T(f)` on the
**strict** function space `(D →⊥ E)` is approximable: there is an approximable map `Φ` from
`(D →⊥ E)` to `(T(D) →⊥ T(E))` whose elementwise action (read through the representation
`strictFunEquiv`) sends each strict map `f` to `T(f)`. -/
def ContinuousOnMaps (T : Endofunctor DomainObj) : Prop :=
  ∀ D E : DomainObj,
    ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
      ∀ f : StrictMap D.sys E.sys,
        (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1
end

section
/-- A functor continuous on maps **preserves strictness** (so it genuinely lives on Scott's category
of domains and strict maps): if `f` is strict then so is `T(f)`. This is automatic from the witnessing
equation, whose left-hand side is the underlying map of a `StrictMap`. -/
theorem ContinuousOnMaps.isStrict_map {T : Endofunctor DomainObj} (h : ContinuousOnMaps T)
    {D E : DomainObj} (f : StrictMap D.sys E.sys) :
    IsStrict (T.map (X := D) (Y := E) f.1) := by
  obtain ⟨Φ, hΦ⟩ := h D E
  rw [← hΦ f]
  exact (toStrictMap (Φ.toElementMap (toStrictFilter f))).2
end

section
/-- `toStrictMap ∘ toStrictFilter = id` (the right inverse of the strict-function-space
representation, Exercise 5.10). -/
theorem toStrictMap_toStrictFilter {α β : Type*} {V₀ : NeighborhoodSystem α}
    {V₁ : NeighborhoodSystem β} (f : StrictMap V₀ V₁) :
    toStrictMap (toStrictFilter f) = f :=
  (strictFunEquiv V₀ V₁).right_inv f
end

section
/-- **The identity functor is continuous on maps** — the basic witness that Definition 6.8 is
satisfiable. The representing approximable map is the identity on `(D →⊥ E)`. -/
theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  show (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/-- Composing the two unique homomorphisms `A → B → A` gives the identity homomorphism on the initial
algebra `A`. -/
theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/- concordance: source L3709 PROPOSITION 6.6 uniqueness of initial algebras -/
/-- **Proposition 6.6 (Scott 1981, PRG-19).** Any two initial `T`-algebras have isomorphic carriers;
the isomorphism is built from the unique homomorphisms in both directions. -/
def initialIso (hA : IsInitial A) (hB : IsInitial B) : Iso A.carrier B.carrier where
  hom := (hA.desc B).hom
  inv := (hB.desc A).hom
  hom_inv_id := by
    have h := comp_desc_eq_id hA hB
    have := congrArg AlgHom.hom h
    simpa using this
  inv_hom_id := by
    have h := comp_desc_eq_id hB hA
    have := congrArg AlgHom.hom h
    simpa using this
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/-- The isomorphism of Proposition 6.6 is **unique**: the homomorphism `A → B` realising it is the
only homomorphism between the two initial algebras. -/
theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h
end

section
set_option linter.unusedVariables false

theorem theorem_66.{u, u_1} : ∀ {Obj : Type u} [inst : CategoryTheory.Category.{u_1, u} Obj]
  {T : @DomainTheory.NeighbourhoodSystems.Endofunctor Obj inst}
  {A B : @DomainTheory.NeighbourhoodSystems.TAlgebra Obj inst T}
  (hA : @DomainTheory.NeighbourhoodSystems.IsInitial Obj inst T A)
  (h : @DomainTheory.NeighbourhoodSystems.AlgHom Obj inst T A B),
  @Eq (@DomainTheory.NeighbourhoodSystems.AlgHom Obj inst T A B) h
    (@DomainTheory.NeighbourhoodSystems.IsInitial.desc Obj inst T A hA B) :=
  @DomainTheory.NeighbourhoodSystems.iso_hom_unique
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- Composition is monotone in both arguments (general arities). -/
theorem comp_mono_gen {a a' : ApproximableMap V₁ V₂} {b b' : ApproximableMap V₀ V₁}
    (ha : a ≤ a') (hb : b ≤ b') : a.comp b ≤ a'.comp b' := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hb _ _ hXY, ha _ _ hYZ⟩
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The composite of strict maps is strict: `(a ∘ b)(⊥) = a(b(⊥)) = a(⊥) = ⊥`. -/
theorem isStrict_comp {a : ApproximableMap V₁ V₂} {b : ApproximableMap V₀ V₁}
    (ha : IsStrict a) (hb : IsStrict b) : IsStrict (a.comp b) := by
  rw [isStrict_iff_apply_bot, toElementMap_comp, isStrict_iff_apply_bot.mp hb,
    isStrict_iff_apply_bot.mp ha]
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- The strict composite `g ↦ k ∘ g ∘ j : (T(D) →⊥ T(E)) → (D →⊥ E)`. -/
def homOpComp (g : StrictMap (T.obj D).sys (T.obj E).sys) : StrictMap D.sys E.sys :=
  ⟨k.comp (g.1.comp j), isStrict_comp hk (isStrict_comp g.2 hj)⟩

end HomOp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

theorem homOpComp_mono {g g' : StrictMap (T.obj D).sys (T.obj E).sys} (hgg : g ≤ g') :
    homOpComp T D E j k hj hk g ≤ homOpComp T D E j k hj hk g' := by
  show k.comp (g.1.comp j) ≤ k.comp (g'.1.comp j)
  exact comp_mono_gen le_rfl (comp_mono_gen (Subtype.coe_le_coe.mpr hgg) le_rfl)

end HomOp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- `toStrictFilter` is monotone. -/
theorem toStrictFilter_mono {f f' : StrictMap V₀ V₁} (h : f ≤ f') :
    toStrictFilter f ≤ toStrictFilter f' := by
  intro W hW
  rw [mem_toStrictFilter] at hW ⊢
  exact ⟨hW.1, strictFun_mem_up_closed hW.1 hW.2 h⟩
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- `toStrictMap` is monotone. -/
theorem toStrictMap_mono {φ φ' : (strictFun V₀ V₁).Element} (h : φ ≤ φ') :
    toStrictMap φ ≤ toStrictMap φ' := by
  intro X Y hrel
  rw [toStrictMap_rel] at hrel ⊢
  exact h _ hrel
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- **The operator `λg. k ∘ g ∘ j`** as an approximable map between the strict function spaces, built
by Exercise 2.8 (`ofMono`) from its values on finite elements. -/
def homOp : ApproximableMap (strictFun (T.obj D).sys (T.obj E).sys) (strictFun D.sys E.sys) :=
  ofMono
    (fun N hN => toStrictFilter (homOpComp T D E j k hj hk
      (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN))))
    (by
      intro N N' hN hN' hN'N
      apply toStrictFilter_mono
      apply homOpComp_mono
      apply toStrictMap_mono
      exact ((strictFun (T.obj D).sys (T.obj E).sys).principal_le_iff hN hN').mpr hN'N)

end HomOp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)


theorem homOp_rel {N : Set (StrictMap (T.obj D).sys (T.obj E).sys)}
    {M : Set (StrictMap D.sys E.sys)} :
    (homOp T D E j k hj hk).rel N M ↔
      ∃ hN : (strictFun (T.obj D).sys (T.obj E).sys).mem N,
        (toStrictFilter (homOpComp T D E j k hj hk
          (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN)))).mem M :=
  Iff.rfl

end HomOp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- If `a ∘ b = I` then `a` is strict: any (split) iso preserves `⊥`. -/
theorem isStrict_of_comp_eq_id {a : ApproximableMap V₁ V₀} {b : ApproximableMap V₀ V₁}
    (h : a.comp b = idMap V₀) : IsStrict a := by
  rw [isStrict_iff_apply_bot]
  refine le_antisymm ?_ (V₀.bot_le _)
  calc a.toElementMap V₁.bot
      ≤ a.toElementMap (b.toElementMap V₀.bot) := toElementMap_mono a (V₁.bot_le _)
    _ = (a.comp b).toElementMap V₀.bot := (toElementMap_comp a b V₀.bot).symm
    _ = V₀.bot := by rw [h, toElementMap_idMap]
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- `toStrictFilter ∘ toStrictMap = id` (the left inverse of the strict-function-space
representation; the mirror of `toStrictMap_toStrictFilter`). -/
theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hWmem, hfW⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
    exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
  · intro hW
    refine ⟨φ.sub hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
    intro p hp
    exact (mem_sstepFun_iff φ hL).mp hW p hp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)


/-- **Action lemma.** `homOp` realizes the composite `g ↦ k ∘ g ∘ j` on filters of strict maps:
`homOp(ĝ) = (k ∘ g ∘ j)^`. Proved by reducing to single step neighbourhoods through the strict
representation. -/
theorem homOp_apply_filter (g : StrictMap (T.obj D).sys (T.obj E).sys) :
    (homOp T D E j k hj hk).toElementMap (toStrictFilter g)
      = toStrictFilter (homOpComp T D E j k hj hk g) := by
  have key : ∀ X Z,
      ((homOp T D E j k hj hk).toElementMap (toStrictFilter g)).mem (sstep X Z)
        ↔ (homOpComp T D E j k hj hk g).1.rel X Z := by
    intro X Z
    constructor
    · rintro ⟨N, hgN, hrel⟩
      rw [homOp_rel] at hrel
      obtain ⟨hN, hmem⟩ := hrel
      rw [mem_toStrictFilter] at hmem
      obtain ⟨_, hsstep⟩ := hmem
      rw [mem_sstep] at hsstep
      obtain ⟨Y2, ⟨Y1, hXY1, hY1Y2⟩, hY2Z⟩ := hsstep
      rw [toStrictMap_rel, mem_principal] at hY1Y2
      obtain ⟨_, hNsub⟩ := hY1Y2
      exact ⟨Y2, ⟨Y1, hXY1, hNsub (mem_toStrictFilter.mp hgN).2⟩, hY2Z⟩
    · intro hrel
      obtain ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩ := hrel
      refine ⟨sstep Y1 Y2, ?_, ?_⟩
      · rw [mem_toStrictFilter]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, hgY1Y2⟩
      · rw [homOp_rel]
        refine ⟨sstep_mem_of_mem (g := g) hgY1Y2, ?_⟩
        rw [mem_toStrictFilter]
        refine ⟨sstep_mem_of_mem (g := homOpComp T D E j k hj hk g)
          ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩, ?_⟩
        rw [mem_sstep]
        refine ⟨Y2, ⟨Y1, hXY1, ?_⟩, hY2Z⟩
        rw [toStrictMap_rel, mem_principal]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, subset_rfl⟩
  have hmap : toStrictMap ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
      = homOpComp T D E j k hj hk g := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Z
    rw [toStrictMap_rel]
    exact key X Z
  have hL := toStrictFilter_toStrictMap
    ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
  rw [hmap] at hL
  exact hL.symm

end HomOp
end

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/- concordance: source L3775 THEOREM 6.9 homomorphism from initial algebra -/
/-- **Theorem 6.9 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D ≅ T(D)` (so `D` is a
`T`-algebra via `i : T(D) → D`), then for any `T`-algebra `B = (E, k)` with `k` strict there is a
homomorphism `D → E`. The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘ j`. -/
theorem nonempty_algHom_of_continuousOnMaps
    (T : Endofunctor DomainObj) (hT : ContinuousOnMaps T)
    {D : DomainObj} (iso : Iso (T.obj D) D)
    (B : TAlgebra T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} := by
  -- `j = i⁻¹` is strict (it is an isomorphism of domains).
  have hji : iso.inv.comp iso.hom = idMap (T.obj D).sys := iso.hom_inv_id
  have hj : IsStrict iso.inv := isStrict_of_comp_eq_id hji
  -- Definition 6.8's witness that `λf. T(f)` is approximable.
  obtain ⟨Φ, hΦ⟩ := hT D B.carrier
  -- the operator `Op = (k ∘ · ∘ j) ∘ T` and its least fixed point.
  set Op := (homOp T D B.carrier iso.inv B.str hj hk).comp Φ with hOp
  set x := Op.fixElement with hx
  set h := toStrictMap x with hh
  let Tg : StrictMap (T.obj D).sys (T.obj B.carrier).sys :=
    ⟨T.map (X := D) (Y := B.carrier) h.1, hT.isStrict_map (D := D) (E := B.carrier) h⟩
  have hfix : Op.toElementMap x = x := toElementMap_fixElement Op
  have hxh : toStrictFilter h = x := toStrictFilter_toStrictMap x
  -- `Φ` sends `h` to the filter of `T(h)`.
  have hTg : toStrictMap (Φ.toElementMap (toStrictFilter h)) = Tg := Subtype.ext (hΦ h)
  have hφ : Φ.toElementMap (toStrictFilter h) = toStrictFilter Tg := by
    rw [← hTg]; exact (toStrictFilter_toStrictMap _).symm
  -- evaluate the operator at the fixed point.
  have hOpx : Op.toElementMap x
      = toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg) := by
    rw [hOp, toElementMap_comp, ← hxh, hφ, homOp_apply_filter]
  have hcompeq : toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg)
      = toStrictFilter h := by
    rw [← hOpx, hfix, hxh]
  have hh' : homOpComp T D B.carrier iso.inv B.str hj hk Tg = h := by
    have h2 := congrArg toStrictMap hcompeq
    rwa [toStrictMap_toStrictFilter, toStrictMap_toStrictFilter] at h2
  -- the fixed-point equation `h = k ∘ T(h) ∘ j`.
  have hcore : B.str.comp ((T.map (X := D) (Y := B.carrier) h.1).comp iso.inv) = h.1 :=
    congrArg Subtype.val hh'
  -- rearrange to the homomorphism square `h ∘ i = k ∘ T(h)`.
  refine ⟨⟨{ hom := h.1, comm := ?_ }, h.2⟩⟩
  show h.1.comp iso.hom = B.str.comp (T.map (X := D) (Y := B.carrier) h.1)
  conv_lhs => rw [← hcore]
  rw [comp_assoc, comp_assoc, hji, comp_idMap]
end

section
set_option linter.unusedVariables false

theorem theorem_69.{u_4} : ∀
  (T :
    @DomainTheory.NeighbourhoodSystems.Endofunctor.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}),
  DomainTheory.NeighbourhoodSystems.ContinuousOnMaps.{u_4} T →
    ∀ {D : DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}}
      (iso :
        @DomainTheory.NeighbourhoodSystems.Iso.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
          D)
      (B :
        @DomainTheory.NeighbourhoodSystems.TAlgebra.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T),
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).carrier
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B) →
        Nonempty.{u_4 + 1}
          (@Subtype.{u_4 + 1}
            (@DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                  (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                  D iso))
              B)
            fun
              (g :
                @DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))
                  B) =>
            @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
              (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                  (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                    (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                    D iso))
                B g)) :=
  DomainTheory.NeighbourhoodSystems.nonempty_algHom_of_continuousOnMaps.{u_4}
end

end DomainTheory.NeighbourhoodSystems
end

section
-- StrictDomainObj.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- An object of Scott's category (Exercise 6.19): a token type, a neighbourhood system on it, and the
standing assumption `∅ ∉ 𝒟` (every neighbourhood is non-empty). -/
structure StrictDomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system. -/
  sys : NeighborhoodSystem carrier
  /-- Scott's standing assumption `∅ ∉ 𝒟`. -/
  nonempty : ∀ X, sys.mem X → X.Nonempty

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- **The category of `∅`-free domains and strict maps.** Morphisms are strict approximable maps
(`StrictMap`, Exercise 5.10); identities and associative composition come from Theorem 2.5, and
strictness is preserved by `isStrict_idMap` / `isStrict_comp`. -/
instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  comp_id f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  assoc f g h := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1).symm
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem StrictDomainObj.id_val (D : StrictDomainObj) :
    ((𝟙 D) : StrictMap D.sys D.sys).1 = ApproximableMap.idMap D.sys := rfl
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem StrictDomainObj.comp_val {D E F : StrictDomainObj}
    (g : (E ⟶ F)) (f : (D ⟶ E)) :
    ((g ⊚ f : StrictMap D.sys F.sys)).1 = g.1.comp f.1 := rfl
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embZero {X : Set α} {p : List Bool} {a : α} :
    (p, a) ∈ embZero X ↔ p = [] ∧ a ∈ X := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embL {P : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embL P ↔ ∃ p', p = true :: p' ∧ (p', a) ∈ P := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embR {Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embR Q ↔ ∃ q', p = false :: q' ∧ (q', a) ∈ Q := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embPair {P Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embPair P Q ↔
      (∃ p', p = true :: p' ∧ (p', a) ∈ P) ∨ (∃ q', p = false :: q' ∧ (q', a) ∈ Q) := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_Gamma {D : NeighborhoodSystem α} {p : List Bool} {a : α} :
    (p, a) ∈ Gamma D ↔ a ∈ D.master := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem Gamma_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    (Gamma D).Nonempty := by
  obtain ⟨a, ha⟩ := hD D.master D.master_mem; exact ⟨([], a), ha⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_inter (P Q P' Q' : Set (List Bool × α)) :
    embPair P Q ∩ embPair P' Q' = embPair (P ∩ P') (Q ∩ Q') := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embPair]
  rcases p with _ | ⟨b, ps⟩
  · simp
  · cases b <;> simp [List.cons.injEq]

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_nonempty {P Q : Set (List Bool × α)} (hP : P.Nonempty) :
    (embPair P Q).Nonempty := by
  obtain ⟨⟨p', a⟩, hP⟩ := hP; exact ⟨(true :: p', a), Or.inl ⟨p', rfl, hP⟩⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_subset {P Q P' Q' : Set (List Bool × α)} :
    embPair P Q ⊆ embPair P' Q' ↔ P ⊆ P' ∧ Q ⊆ Q' := by
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨p', a⟩ := t
      have hmem : ((true :: p', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inl ⟨p', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', hP'⟩ | ⟨q'', hq'', -⟩
      · simp only [List.cons.injEq, true_and] at hp''; exact hp'' ▸ hP'
      · exact absurd hq'' (by simp)
    · obtain ⟨q', a⟩ := t
      have hmem : ((false :: q', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inr ⟨q', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', -⟩ | ⟨q'', hq'', hQ'⟩
      · exact absurd hp'' (by simp)
      · simp only [List.cons.injEq, true_and] at hq''; exact hq'' ▸ hQ'
  · rintro ⟨hP, hQ⟩ t ht
    rcases ht with ⟨p', hp', hPmem⟩ | ⟨q', hq', hQmem⟩
    · exact Or.inl ⟨p', hp', hP hPmem⟩
    · exact Or.inr ⟨q', hq', hQ hQmem⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_injective {P Q P' Q' : Set (List Bool × α)}
    (h : embPair P Q = embPair P' Q') : P = P' ∧ Q = Q' := by
  obtain ⟨hP, hQ⟩ := embPair_subset.mp h.subset
  obtain ⟨hP', hQ'⟩ := embPair_subset.mp h.symm.subset
  exact ⟨Set.Subset.antisymm hP hP', Set.Subset.antisymm hQ hQ'⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_subset_Gamma {D : NeighborhoodSystem α} {P Q : Set (List Bool × α)}
    (hP : P ⊆ Gamma D) (hQ : Q ⊆ Gamma D) : embPair P Q ⊆ Gamma D := by
  rintro ⟨p, a⟩ (⟨p', -, hPmem⟩ | ⟨q', -, hQmem⟩)
  · have h := hP hPmem; exact h
  · have h := hQ hQmem; exact h

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_inter (X X' : Set α) :
    embZero X ∩ embZero X' = embZero (X ∩ X' : Set α) := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero]
  tauto

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_inter_embPair (X : Set α) (P Q : Set (List Bool × α)) :
    embZero X ∩ embPair P Q = ∅ := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero, mem_embPair, Set.mem_empty_iff_false, iff_false,
    not_and, not_or]
  rintro ⟨rfl, -⟩
  exact ⟨by rintro ⟨p', hp', -⟩; exact absurd hp' (by simp), by rintro ⟨q', hq', -⟩; exact absurd hq' (by simp)⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_nonempty {X : Set α} (hX : X.Nonempty) : (embZero X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨([], a), rfl, ha⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_subset {X X' : Set α} : embZero X ⊆ embZero X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha
    have : (([], a) : List Bool × α) ∈ embZero X' := h ⟨rfl, ha⟩
    exact this.2
  · intro h t ht; exact ⟨ht.1, h ht.2⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_injective {X X' : Set α} (h : embZero X = embZero X') : X = X' :=
  Set.Subset.antisymm (embZero_subset.mp h.subset) (embZero_subset.mp h.symm.subset)

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_subset_Gamma {D : NeighborhoodSystem α} {X : Set α} (hX : D.mem X) :
    embZero X ⊆ Gamma D := by
  rintro ⟨p, a⟩ ⟨-, ha⟩; exact D.sub_master hX ha

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Under Scott's standing assumption `∅ ∉ 𝒟`, no neighbourhood of `D^§` is empty. -/
theorem memS_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {W : Set (List Bool × α)} (hW : MemS D W) : W.Nonempty := by
  induction hW with
  | gamma => exact Gamma_nonempty hD
  | zero hX => exact embZero_nonempty (hD _ hX)
  | pair _ _ ihP _ => exact embPair_nonempty ihP

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Every neighbourhood of `D^§` is a subset of the master `Γ` (Scott's `𝒟^§ ⊆ 𝒫(Γ)`). -/
theorem memS_subset_gamma {D : NeighborhoodSystem α} {W : Set (List Bool × α)}
    (hW : MemS D W) : W ⊆ Gamma D := by
  induction hW with
  | gamma => exact subset_rfl
  | zero hX => exact embZero_subset_Gamma hX
  | pair _ _ ihP ihQ => exact embPair_subset_Gamma ihP ihQ

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 — closure under consistent intersection.** Scott's central verification, "by
induction on the number of steps required to put `X` and `Y` into `𝒟^§`". The cross cases
(`0A ∩ (1P∪2Q) = ∅`, etc.) are discharged because the consistency witness `Z` is non-empty
(`memS_nonempty`); the `0A ∩ 0B` case uses `𝒟`'s own closure; the `(1P∪2Q) ∩ (1P'∪2Q')` case recurses
on `P, P'` and `Q, Q'`. -/
theorem memS_inter {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ {X : Set (List Bool × α)}, MemS D X → ∀ {Y : Set (List Bool × α)}, MemS D Y →
      ∀ {Z : Set (List Bool × α)}, MemS D Z → Z ⊆ X ∩ Y → MemS D (X ∩ Y) := by
  intro X hX
  induction hX with
  | gamma =>
    intro Y hY Z _ _
    rw [Set.inter_eq_right.mpr (memS_subset_gamma hY)]; exact hY
  | @zero A hA =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hA)]; exact MemS.zero hA
    | @zero B hB =>
      rw [embZero_inter]
      -- the witness `Z` must be a `0C`; read off `C ⊆ A ∩ B`, then `D`'s closure gives `A ∩ B ∈ 𝒟`.
      rw [embZero_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        exact MemS.zero (D.inter_mem hA hB hC (embZero_subset.mp hsub))
      | @pair P Q hP hQ =>
        obtain ⟨t, hmem⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hempty : t.1 = [] := (hsub hmem).1
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · rw [hp'] at hempty; exact absurd hempty (by simp)
        · rw [hq'] at hempty; exact absurd hempty (by simp)
    | @pair P Q _ _ =>
      rw [embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
  | @pair P Q hP hQ ihP ihQ =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))]
      exact MemS.pair hP hQ
    | @zero B hB =>
      rw [Set.inter_comm, embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
    | @pair P' Q' hP' hQ' =>
      rw [embPair_inter]
      rw [embPair_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        obtain ⟨a, ha⟩ := hD C hC
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ embZero C from ⟨rfl, ha⟩)) (by simp)
      | @pair Z₀ Z₁ hZ₀ hZ₁ =>
        obtain ⟨hsub₀, hsub₁⟩ := embPair_subset.mp hsub
        exact MemS.pair (ihP hP' hZ₀ hsub₀) (ihQ hQ' hZ₁ hsub₁)

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 (Scott 1981, PRG-19).** The *tree algebra* `D^§`: a neighbourhood system over
`Γ = {1,2}* 0 Δ`, under the standing assumption `∅ ∉ 𝒟` (`hD`). -/
abbrev Dsharp (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem (List Bool × α) where
  mem := MemS D
  master := Gamma D
  master_nonempty := by
    obtain ⟨a, ha⟩ := D.master_nonempty
    exact ⟨([], a), ha⟩
  master_mem := MemS.gamma
  inter_mem := fun hX hY hZ hsub => memS_inter hD hX hY hZ hsub
  sub_master := memS_subset_gamma

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem Dsharp_mem {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty}
    {W : Set (List Bool × α)} : (Dsharp D hD).mem W ↔ MemS D W := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem Dsharp_master {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty} :
    (Dsharp D hD).master = Gamma D := rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embPair_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {P Q : Set (List Bool × α)} (h : MemS D (embPair P Q)) : MemS D P ∧ MemS D Q := by
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : (([], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1
    rcases h1 with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · simp at hp'
    · simp at hq'
  | @zero X hX =>
    exfalso
    obtain ⟨t, ht⟩ := embZero_nonempty (hD X hX)
    have hempty : t.1 = [] := ht.1
    rw [← hW] at ht
    rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · rw [hp'] at hempty; simp at hempty
    · rw [hq'] at hempty; simp at hempty
  | @pair P' Q' hP' hQ' =>
    obtain ⟨hPP, hQQ⟩ := embPair_injective hW
    rw [hPP, hQQ]; exact ⟨hP', hQ'⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embZero_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α}
    (h : MemS D (embZero X)) : D.mem X := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1; exact absurd h1.1 (by simp)
  | @zero X' hX' => rw [embZero_injective hW]; exact hX'
  | @pair P Q hP hQ =>
    exfalso
    obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
    have hcons : t.1 ≠ [] := by
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp [hp']
      · simp [hq']
    have hz : t ∈ embZero X := by rw [← hW] at ht; exact ht
    exact hcons hz.1

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of `D^§ × D^§` is empty (needed to form the sum `D + (D^§ × D^§)`). -/
theorem prod_dsharp_nonempty :
    ∀ V, (prod (Dsharp D hD) (Dsharp D hD)).mem V → V.Nonempty := by
  rintro V ⟨P, Q, hP, hQ, rfl⟩
  obtain ⟨t, ht⟩ := memS_nonempty hD hP
  exact ⟨Sum.inl t, mem_prodNbhd_inl.mpr ht⟩

end Equation

end Example61
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

/-- The family of **neighbourhood-sets of subdomains of `E`**: a set of subsets of `Δ` lies in
`subFam E` exactly when it is `{X ∣ D.mem X}` for some subsystem `D ◁ E`. This is the concrete
family of sets that, by Exercise 2.22, represents `{D ∣ D ◁ E}` as a domain. -/
def subFam (E : NeighborhoodSystem α) : Set (Set (Set α)) :=
  {𝒮 | ∃ D : NeighborhoodSystem α, D ◁ E ∧ 𝒮 = {X | D.mem X}}
end

section
variable {α : Type*}

/-- Consistency is inherited from `E` (Definition 6.10's essential clause): if `X, Y` lie in a
subdomain's neighbourhood-set and `X ∩ Y ∈ E`, then `X ∩ Y` lies in it too. -/
theorem subFam_inter_closed (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X Y : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : E.mem (X ∩ Y)) : X ∩ Y ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.inter_closed hX hY hXY
end

section
variable {α : Type*}

/-- The master `Δ = E.master` belongs to the neighbourhood-set of any subdomain (a subsystem shares
`E`'s master and contains it). -/
theorem subFam_master_mem (E : NeighborhoodSystem α) {𝒮 : Set (Set α)}
    (h : 𝒮 ∈ subFam E) : E.master ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  rw [← hD.master_eq]
  exact D.master_mem
end

section
variable {α : Type*}

/-- Every member of a subdomain's neighbourhood-set is an `E`-neighbourhood (`D ⊆ E`). -/
theorem subFam_mem_E (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) : E.mem X := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.sub hX
end

section
variable {α : Type*}

/-- The **intersection subdomain** of a non-empty family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are the sets common to *every* member of `ℱ`. -/
def interSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : NeighborhoodSystem α where
  mem X := ∀ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := fun 𝒮 h𝒮 => subFam_master_mem E (hℱ h𝒮)
  inter_mem := by
    intro X Y Z hX hY hZ hsub 𝒮 h𝒮
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮) (hY 𝒮 h𝒮)
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮) (hZ 𝒮 h𝒮)
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) (E.inter_mem hEX hEY hEZ hsub)
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮))
end

section
variable {α : Type*}

/-- The neighbourhood-set of the intersection subdomain is exactly `⋂₀ ℱ`. -/
theorem interSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) :
    {X | (interSys E ℱ hne hℱ).mem X} = ⋂₀ ℱ := by
  ext X
  exact Set.mem_sInter.symm
end

section
variable {α : Type*}

/-- The intersection subdomain is a subsystem of `E`. -/
theorem interSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : interSys E ℱ hne hℱ ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
  inter_closed := by
    intro X Y hX hY hEXY 𝒮 h𝒮
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) hEXY
end

section
variable {α : Type*}

/-- Rebuild a subsystem of `E` from its neighbourhood-set `𝒮 ∈ subFam E`. The data (the `mem`
predicate `· ∈ 𝒮` and the master `E.master`) depends only on `𝒮`; the proof obligations are
discharged from `subFam` membership. -/
def ofMem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    NeighborhoodSystem α where
  mem X := X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := subFam_master_mem E h
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    exact subFam_inter_closed E h hX hY
      (E.inter_mem (subFam_mem_E E h hX) (subFam_mem_E E h hY) (subFam_mem_E E h hZ) hsub)
  sub_master := fun hX => E.sub_master (subFam_mem_E E h hX)
end

section
variable {α : Type*}

/-- `ofMem` lands in the subsystems of `E`. -/
theorem ofMem_subsystem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    ofMem E 𝒮 h ◁ E where
  master_eq := rfl
  sub := subFam_mem_E E h
  inter_closed := subFam_inter_closed E h
end

section
variable {α : Type*}

end

section
set_option linter.unusedVariables false

theorem theorem_611.{u_1} : ∀ {α : Type u_1} (E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (𝒮 : Set (Set α))
  (h :
    @Membership.mem (Set (Set α)) (Set (Set (Set α))) (@Set.instMembership (Set (Set α)))
      (@DomainTheory.NeighbourhoodSystems.Proposition611.subFam α E) 𝒮),
  @DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.Proposition611.ofMem α E 𝒮 h) E :=
  @DomainTheory.NeighbourhoodSystems.Proposition611.ofMem_subsystem
end

end DomainTheory.NeighbourhoodSystems.Proposition611
end

section
-- Definition613/MonotoneAt.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Definition 6.13, monotone part (pointwise).** Given a subdomain relation `h : D ◁ E`, the data
witnessing that the functor `T` carries it to `T(D) ◁ T(E)` *and* carries the projection pair `i, j`
of 6.12 to the projection pair of `T(D) ◁ T(E)`.

Because `T` may change the token type, the two image systems live a priori over different carriers;
`carrier_eq` records that they coincide, `sub` is the resulting subdomain relation (with `T(E)`'s
system transported into `T(D)`'s carrier), and `inj_heq`/`proj_heq` say the canonical 6.12 maps of
`sub` are `T(i)` and `T(j)` (up to that transport, hence `HEq`). -/
structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  /-- The two image carriers coincide, so `T(D) ◁ T(E)` can be stated. -/
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  /-- The image subdomain relation `T(D) ◁ T(E)` (with `T(E)`'s system carried into `T(D)`'s
  carrier). -/
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  /-- The injection of `T(D) ◁ T(E)` is `T(i)` (Scott: the pair is mapped to `T(i), T(j)`). -/
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  /-- The projection of `T(D) ◁ T(E)` is `T(j)`. -/
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
universe w

/- concordance: source L3849 DEFINITION 6.13 continuity on domains -/
/-- **Definition 6.13 (Scott 1981, PRG-19), monotone on domains.** A functor `T` is *monotone on
domains* iff every subdomain relation `D ◁ E` is carried to a subdomain relation `T(D) ◁ T(E)` whose
projection pair is `(T(i), T(j))` — see `MonotoneAt`. -/
def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h
end

section
universe w

/-- The **target-side neighbourhood family** of the image `T(D)` of a subsystem `h : D ◁ E`, viewed
over `T(E)`'s carrier (using `MonotoneAt.carrier_eq` to transport neighbourhoods of `T(D)` to that
carrier). This is the data on which "`λD. T(D)` is approximable" is expressed. -/
def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}
end

section
universe w

/-- **Definition 6.13 (Scott 1981, PRG-19), continuous on domains.** A monotone functor `T` is
*continuous on domains* iff `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is approximable. In the
neighbourhood framework this is *preservation of directed unions of subsystems*: for any non-empty
directed family `ℱ` of subsystems of `E` whose union is the subsystem `U` (`hU`), the target-side
neighbourhood family of `T(U)` is the union of those of the `T(D)` for `D ∈ ℱ`. -/
def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)
end

section
/-- The **identity functor is monotone on domains**: it fixes objects and maps, so `T(D) ◁ T(E)` is
just `D ◁ E` and the projection pair is unchanged. -/
theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩
end

section
/-- The **identity functor is continuous on domains**: `targetFam` reduces to the plain neighbourhood
family, so directed-union preservation is exactly the hypothesis `hU` that `U` is the union. -/
theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y
end

namespace Exercise619
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
/-- **An object of the Exercise 6.19 category.** An `∅`-free neighbourhood system over
`Str = {0,1}*` (`ne`: every neighbourhood is non-empty, Scott's `∅ ∉ 𝒟`). -/
structure ScottSys where
  /-- The underlying neighbourhood system on `{0,1}*`. -/
  sys : NeighborhoodSystem Str
  /-- `∅ ∉ 𝒟`: every neighbourhood is non-empty. -/
  ne : ∀ X, sys.mem X → X.Nonempty
end

end Exercise619
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The functor-expression algebra.** A `T(X)` built from constants, the identity, and binary sums
and products — Scott's closed family of constructs. -/
inductive FExpr where
  | const : ScottSys → FExpr
  | var : FExpr
  | sum : FExpr → FExpr → FExpr
  | prod : FExpr → FExpr → FExpr

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- A non-empty `b`-tagged copy can never sit inside a `b'`-tagged copy for `b ≠ b'`. -/
theorem embBit_not_subset_cross {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty)
    (hsub : embBit b X ⊆ embBit b' Y) : False := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨w', he, -⟩ := hsub ⟨t, rfl, ht⟩
  simp only [List.cons.injEq] at he
  exact h he.1

end Exercise619
end

section
namespace Exercise619

/-- The **product object** `𝒟₀ × 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.prod (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨prodTok A₀.sys A₁.sys, prodTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **`f₀ × f₁`, the action of the product functor on (approximable) maps.** A product
neighbourhood `{Λ} ∪ 0X ∪ 1Y` is sent to `{Λ} ∪ 0X' ∪ 1Y'` whenever `X f₀ X'` and `Y f₁ Y'`. -/
def prodMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.prod A₁).sys (B₀.prod B₁).sys where
  rel W W' := ∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧
    W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y'
  rel_dom := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, rfl, -⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_dom h0) (f₁.rel_dom h1)
  rel_cod := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, -, rfl⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_cod h0) (f₁.rel_cod h1)
  master_rel :=
    ⟨A₀.sys.master, A₁.sys.master, B₀.sys.master, B₁.sys.master,
      f₀.master_rel, f₁.master_rel, rfl, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ ⟨X₂, Y₂, X'₂, Y'₂, h0₂, h1₂, hWeq, rfl⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right h0 h0₂, f₁.inter_right h1 h1₂, rfl,
      prodTokNbhd_inter X' X'₂ Y' Y'₂⟩
  mono := by
    rintro W W'' Z Z' ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ hWW hZZ' hW'' hZ'
    obtain ⟨X₂, Y₂, hX₂, hY₂, rfl⟩ := hW''
    obtain ⟨X'₃, Y'₃, hX'₃, hY'₃, rfl⟩ := hZ'
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hWW
    obtain ⟨hsX', hsY'⟩ := prodTokNbhd_subset_iff.mp hZZ'
    exact ⟨X₂, Y₂, X'₃, Y'₃, f₀.mono h0 hsX hsX' hX₂ hX'₃, f₁.mono h1 hsY hsY' hY₂ hY'₃, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The one-neighbourhood system `{Γ}`** over `{0,1}*`: its only neighbourhood is `Γ` itself, and
its master (token set) is `Γ`. It is `∅`-free precisely because `Γ` is non-empty. -/
def singletonSys (Γ : Set Str) (h : Γ.Nonempty) : ScottSys where
  sys :=
    { mem := fun X => X = Γ
      master := Γ
      master_nonempty := h
      master_mem := rfl
      inter_mem := by
        intro X Y Z hX hY _ _
        show X ∩ Y = Γ
        rw [hX, hY, Set.inter_self]
      sub_master := by intro X hX; rw [show X = Γ from hX] }
  ne := by intro X hX; rw [show X = Γ from hX]; exact h

end Exercise619
end

section
namespace Exercise619

/-- The **sum object** `𝒟₀ + 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.sum (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨sumTok A₀.sys A₁.sys A₀.ne A₁.ne, sumTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** This is what keeps the bottom `{Λ}` and
the whole Kleene chain inside the domain `{Γ ∣ Λ ∈ Γ}`; sums and products satisfy it for free. -/
def FExpr.RootedConst : FExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The token-level master recursion.** `mFun T Γ` computes `tok(T({Γ}))` purely from `Γ`, without
touching the neighbourhood data of `{Γ}` (`mFun_eq_master`): constants are constant, the identity
returns `Γ`, and both sum and product wrap the two component token sets with the tags `0,1` under a
common root `Λ` (`sumTokMaster = prodTokNbhd` agree on masters). -/
def mFun : FExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
  | .prod T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- The **Kleene iteration** `mFunⁿ({Λ})` whose union is the least fixed point above `{Λ}`. -/
def mIter (T : FExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => mFun T (mIter T n)

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The action of `T` on objects.** -/
def FExpr.obj : FExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum T₀ T₁, X => (T₀.obj X).sum (T₁.obj X)
  | .prod T₀ T₁, X => (T₀.obj X).prod (T₁.obj X)

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **`f₀ + f₁`, the action of the sum functor on (approximable) maps.** It carries the master to the
master (so it is strict), a left copy `0X` to `0X'` whenever `X f₀ X'`, and a right copy `1Y` to
`1Y'` whenever `Y f₁ Y'`. -/
def sumMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.sum A₁).sys (B₀.sum B₁).sys where
  rel W W' :=
    ((sumTok A₀.sys A₁.sys A₀.ne A₁.ne).mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩ | ⟨Y, Y', hrel, rfl, -⟩)
    · exact hW
    · exact Or.inr (Or.inl ⟨X, f₀.rel_dom hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, f₁.rel_dom hrel, rfl⟩)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩ | ⟨Y, Y', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X', f₀.rel_cod hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y', f₁.rel_cod hrel, rfl⟩)
  master_rel := Or.inl ⟨(A₀.sum A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩ | ⟨Y, Y', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hWeq, by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hWeq, by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, rfl, embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · -- output was the master; a blunter neighbourhood must again be the master.
      exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.sum B₁).sys.sub_master hZ') hZZ'⟩
    · -- input `0X`, output `0X'`. The sharper input `W''` and blunter output `Z'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · -- input `1Y`, output `1Y'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The action of `T` on (approximable) maps.** Constants act by the identity, the identity functor
acts by `f` itself, and sums/products act by the bifunctorial combinators `sumMapTok`/`prodMapTok`. -/
def FExpr.map : (T : FExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum T₀ T₁, _, _, f => sumMapTok (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f => prodMapTok (T₀.map f) (T₁.map f)

end Exercise619
end

section
namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **`tok(𝒟)`** — the underlying set of tokens of a system, i.e. its master neighbourhood `Δ`. -/
def ScottSys.tok (D : ScottSys) : Set Str := D.sys.master

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- `mFun T Γ` is exactly the token set `tok(T({Γ})) = (T.obj {Γ}).sys.master`. -/
theorem mFun_eq_master : (T : FExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    mFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]
  | .prod T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]

/-- Monotonicity of the tagged-union shape shared by sum and product. -/
theorem insertTag_mono {p q p' q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') :
    insert ([] : Str) (embBit false p ∪ embBit true q)
      ⊆ insert ([] : Str) (embBit false p' ∪ embBit true q') := by
  rintro w (rfl | hw | hw)
  · exact Or.inl rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

/-- **`λΓ. tok(T({Γ}))` is monotone on the domain.** -/
theorem mFun_mono (T : FExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : mFun T Γ ⊆ mFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-- Continuity (full additivity) of the tagged-union shape shared by sum and product. -/
theorem insertTag_continuous {ℱ : Set (Set Str)} {U : Set Str} (hne : ℱ.Nonempty)
    {p q : Set Str → Set Str}
    (hp : ∀ w, w ∈ p U ↔ ∃ Γ ∈ ℱ, w ∈ p Γ)
    (hq : ∀ w, w ∈ q U ↔ ∃ Γ ∈ ℱ, w ∈ q Γ) (w : Str) :
    (w ∈ insert ([] : Str) (embBit false (p U) ∪ embBit true (q U)))
      ↔ ∃ Γ ∈ ℱ, w ∈ insert ([] : Str) (embBit false (p Γ) ∪ embBit true (q Γ)) := by
  simp only [Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro (rfl | hw | hw)
    · obtain ⟨Γ, hΓ⟩ := hne; exact ⟨Γ, hΓ, Or.inl rfl⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hpΓ⟩ := (hp w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inl ⟨w', rfl, hpΓ⟩)⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hqΓ⟩ := (hq w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inr ⟨w', rfl, hqΓ⟩)⟩
  · rintro ⟨Γ, hΓ, (rfl | hw | hw)⟩
    · exact Or.inl rfl
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inl ⟨w', rfl, (hp w').mpr ⟨Γ, hΓ, hw'⟩⟩)
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inr ⟨w', rfl, (hq w').mpr ⟨Γ, hΓ, hw'⟩⟩)

/-- **`λΓ. tok(T({Γ}))` is continuous on the domain `{Γ ∣ Λ ∈ Γ}`.** For a non-empty `⊆`-directed
family `ℱ` with union `U`, the token set of `T({U})` is the union of those of the `T({Γ})`. (The
proof in fact establishes full additivity — directedness is not needed for the master level — but the
statement is the directed-sup form Scott calls *continuous*.) -/
theorem mFun_continuous (T : FExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ mFun T U ↔ ∃ Γ ∈ ℱ, w ∈ mFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w


/-- If `Λ ∈ Γ` then `Λ ∈ tok(T({Γ}))` — so `λΓ. tok(T({Γ}))` is an endofunction of the domain. -/
theorem mFun_nil_mem : ∀ (T : FExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ mFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _


theorem nil_mem_mIter (T : FExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ mIter T n
  | 0 => rfl
  | n + 1 => mFun_nil_mem T hT (nil_mem_mIter T hT n)

theorem mIter_mono_step (T : FExpr) (hT : T.RootedConst) :
    ∀ n, mIter T n ⊆ mIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact mFun_nil_mem T hT rfl
  | n + 1 => mFun_mono T (mIter_mono_step T hT n)

theorem mIter_mono (T : FExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    mIter T m ⊆ mIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact mIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem mFun_iter_fixed (T : FExpr) (hT : T.RootedConst) :
    mFun T (⋃ n, mIter T n) = ⋃ n, mIter T n := by
  have hstep := mIter_mono_step T hT
  have hne : (Set.range (mIter T)).Nonempty := ⟨mIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (mIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨mIter T (max i j), ⟨max i j, rfl⟩,
      mIter_mono T hT (le_max_left i j), mIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, mIter T n) ↔ ∃ S ∈ Set.range (mIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨mIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [mFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨mIter T n, ⟨n, rfl⟩, hstep n hn⟩

/- concordance: source L4099 EXERCISE 6.20 tokens of a functor -/
/-- **The conclusion of Exercise 6.20 (token level).** For any construct `T` whose constants contain
`Λ`, there is a set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem exists_tok_fixedPoint (T : FExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ mFun T Γ = Γ :=
  ⟨⋃ n, mIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_mIter T hT 0⟩, mFun_iter_fixed T hT⟩

/-- **The conclusion of Exercise 6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies.**
From the fixed point `Γ = tok(T({Γ}))`, the one-neighbourhood system `{Γ}` is a subsystem of
`T({Γ})`: they share the master `Γ`, and `Γ` is a (the master) neighbourhood of `T({Γ})`. -/
theorem exists_singleton_subsystem (T : FExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := exists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  -- `tok(T({Γ})) = Γ` (note `tok` is definitionally `.sys.master`).
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (mFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · -- master_eq: `Γ = tok(T({Γ}))`
    exact hmaster.symm
  · -- sub: the only neighbourhood `Γ` of `{Γ}` is the master of `T({Γ})`
    intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · -- inter_closed: trivial, both neighbourhoods are `Γ`
    intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]
end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`(g₀ ∘ f₀) × (g₁ ∘ f₁) = (g₀ × g₁) ∘ (f₀ × f₁)`.** -/
theorem prodMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    prodMapTok (g₀.comp f₀) (g₁.comp f₁) = (prodMapTok g₀ g₁).comp (prodMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩
    exact ⟨prodTokNbhd X' Y', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩,
      ⟨X', Y', X'', Y'', hg0, hg1, rfl, rfl⟩⟩
  · rintro ⟨W', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩, ⟨X₂, Y₂, X'', Y'', hg0, hg1, hWeq, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`(I_{𝒟₀} × I_{𝒟₁}) = I_{𝒟₀×𝒟₁}`.** -/
theorem prodMapTok_id :
    prodMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.prod A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`prodMapTok` is strict** exactly when both components are strict. -/
theorem prodMapTok_isStrict {f₀ : ApproximableMap A₀.sys B₀.sys}
    {f₁ : ApproximableMap A₁.sys B₁.sys} (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) :
    IsStrict (prodMapTok f₀ f₁) := by
  rintro Y ⟨X, Y0, X', Y', h0, h1, hWeq, rfl⟩
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
  rw [hf₀ h0, hf₁ h1]
  rfl

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- `prodMapTok` is monotone in both arguments. -/
theorem prodMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    prodMapTok f₀ f₁ ≤ prodMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' ⟨X, Y, X', Y', hr0, hr1, rfl, rfl⟩
  exact ⟨X, Y, X', Y', h0 X X' hr0, h1 Y Y' hr1, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- The product carries the subsystem relation componentwise. -/
theorem prodTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.prod A₁).sys ◁ (B₀.prod B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, h0.sub hX, h1.sub hY, rfl⟩
  · rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hInt
    rw [prodTokNbhd_inter] at hInt ⊢
    obtain ⟨X'', Y'', hX'', hY'', heq⟩ := hInt
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hX'', h1.inter_closed hY hY' hY'', rfl⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_619_part_b : ∀ {A₀ A₁ B₀ B₁ : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
  @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str A₀.sys B₀.sys →
    @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str A₁.sys B₁.sys →
      @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str (A₀.prod A₁).sys
        (B₀.prod B₁).sys :=
  @DomainTheory.NeighbourhoodSystems.Exercise619.prodTok_subsystem
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`(g₀ ∘ f₀) + (g₁ ∘ f₁) = (g₀ + g₁) ∘ (f₀ + f₁)`.** -/
theorem sumMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    sumMapTok (g₀.comp f₀) (g₁.comp f₁) = (sumMapTok g₀ g₁).comp (sumMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩ | ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.sum B₁).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, rfl, rfl⟩)⟩
    · exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩ | ⟨Y, Y', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y, Y', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩ | ⟨Y₂, Y'', hg, heq, -⟩
      · exact Or.inl ⟨Or.inr (Or.inl ⟨X, f₀.rel_dom hf, rfl⟩), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, -⟩ | ⟨Y₂, Y'', hg, heq, rfl⟩
      · exact Or.inl ⟨Or.inr (Or.inr ⟨Y, f₁.rel_dom hf, rfl⟩), rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)`.** Every construct `T` preserves composition; together
with `map_id` this shows *these are all functors*. -/
theorem FExpr.map_comp : (T : FExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    (g : ApproximableMap Y.sys Z.sys) → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _ => rfl
  | .sum T₀ T₁, _, _, _, f, g => by
      show sumMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (sumMapTok (T₀.map g) (T₁.map g)).comp (sumMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, sumMapTok_comp]
  | .prod T₀ T₁, _, _, _, f, g => by
      show prodMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (prodMapTok (T₀.map g) (T₁.map g)).comp (prodMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, prodMapTok_comp]

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`(I_{𝒟₀} + I_{𝒟₁}) = I_{𝒟₀+𝒟₁}`.** -/
theorem sumMapTok_id :
    sumMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.sum A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, (A₀.sum A₁).sys.sub_master hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** Every construct `T` preserves identities. -/
theorem FExpr.map_id : (T : FExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const D, _ => rfl
  | .var, _ => rfl
  | .sum T₀ T₁, X => by
      show sumMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).sum (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, sumMapTok_id]
  | .prod T₀ T₁, X => by
      show prodMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).prod (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, prodMapTok_id]

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`sumMapTok` is strict** for *any* component maps: the master input `Λ` (the only neighbourhood
containing the empty string) relates only to the output master. -/
theorem sumMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (sumMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y0, Y', -, heq, -⟩)
  · rfl
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit false X := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit true Y0 := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **Every `T` preserves strictness** (so it restricts to Scott's category of strict maps): `T(f)`
is strict whenever `f` is (and constants/sums are strict unconditionally). -/
theorem FExpr.map_isStrict : (T : FExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum T₀ T₁, _, _, f, _ => sumMapTok_isStrict (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f, hf =>
      prodMapTok_isStrict (T₀.map_isStrict f hf) (T₁.map_isStrict f hf)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- `sumMapTok` is monotone in both arguments. -/
theorem sumMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    sumMapTok f₀ f₁ ≤ sumMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`λf. T(f)` is monotone.** A sharper map `f ≤ f'` is sent to a sharper image `T(f) ≤ T(f')` —
the monotonicity half of *continuous on maps*. -/
theorem FExpr.map_mono : (T : FExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum T₀ T₁, _, _, _, _, h => sumMapTok_mono (T₀.map_mono h) (T₁.map_mono h)
  | .prod T₀ T₁, _, _, _, _, h => prodMapTok_mono (T₀.map_mono h) (T₁.map_mono h)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- Forward direction of continuity on maps: a related pair of `T(f)` is already related by some
`T(gᵢ)`. -/
theorem FExpr.map_continuous_mp : (T : FExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := T₁.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := T₁.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (T₀.map_mono hik) P P' hi, (T₁.map_mono hjk) Q Q' hj, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`λf. T(f)` is continuous on maps.** For a non-empty directed family `gᵢ` with pointwise union
`f`, the relation of `T(f)` is the union of those of the `T(gᵢ)` — `T(f)` is approximable. -/
theorem FExpr.map_continuous (T : FExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- The sum carries the subsystem relation componentwise: `𝒟₀ ◁ ℰ₀` and `𝒟₁ ◁ ℰ₁` give
`𝒟₀+𝒟₁ ◁ ℰ₀+ℰ₁`. -/
theorem sumTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.sum A₁).sys ◁ (B₀.sum B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) (rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (sumTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (sumTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`λX. T(X)` is monotone on domains.** Whenever `X ◁ Y` we have `T(X) ◁ T(Y)`. -/
theorem FExpr.obj_subsystem : (T : FExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum T₀ T₁, _, _, h => sumTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)
  | .prod T₀ T₁, _, _, h => prodTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- Forward direction of continuity on domains: a neighbourhood of `T(U)` is a neighbourhood of some
`T(D)` with `D ∈ ℱ`. -/
theorem FExpr.obj_continuous_mp : (T : FExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((FExpr.sum T₀ T₁).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (T₀.obj_subsystem hr1).sub hXD, (T₁.obj_subsystem hr2).sub hYD, rfl⟩

end Exercise619
end

section
namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`λD. T(D)` is continuous on domains.** For a non-empty `◁`-directed family `ℱ` of subsystems of
`U` whose union is `U`, the neighbourhood family of `T(U)` is the union of those of the `T(D)`. -/
theorem FExpr.obj_continuous (T : FExpr) {ℱ : Set ScottSys} {U : ScottSys}
    (hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ) (hne : ℱ.Nonempty)
    (hsub : ∀ D ∈ ℱ, D.sys ◁ U.sys) (hU : ∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X)
    (W : Set Str) : (T.obj U).sys.mem W ↔ ∃ D ∈ ℱ, (T.obj D).sys.mem W := by
  refine ⟨T.obj_continuous_mp hdir hne hsub hU, ?_⟩
  rintro ⟨D, hD, hmem⟩
  exact (T.obj_subsystem (hsub D hD)).sub hmem

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}
variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}
variable {A₀ A₁ B₀ B₁ : ScottSys}
variable {C₀ C₁ : ScottSys}

/-- **The extended functor-expression algebra** (constants, identity, `+`, `×`, `⊕`, `⊗`). -/
inductive GExpr where
  | const : ScottSys → GExpr
  | var : GExpr
  | sum : GExpr → GExpr → GExpr
  | prod : GExpr → GExpr → GExpr
  | oplus : GExpr → GExpr → GExpr
  | otimes : GExpr → GExpr → GExpr

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- If `X ⊆ Δ` and `X ≠ Δ`, then any intersection `X ∩ X'` is still `≠ Δ` (it is `⊆ X ⊊ Δ`). -/
theorem inter_ne_of_ne_left {X X' Δ : Set Str} (hX : X ⊆ Δ) (hne : X ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX (by rw [← h]; exact Set.inter_subset_left))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **Right-nested n-ary fold** of a binary construct-operation `op` over a non-empty list `a, l…`.
With `op = .sum`/`.prod`/`.oplus`/`.otimes` this is the n-ary `+`/`×`/`⊕`/`⊗`. -/
def GExpr.naryOp (op : GExpr → GExpr → GExpr) (a : GExpr) : List GExpr → GExpr
  | [] => a
  | b :: l => op a (GExpr.naryOp op b l)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- n-ary separated product `T₀ × T₁ × ⋯ × Tₙ`. -/
def GExpr.naryProd : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.prod

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- n-ary separated sum `T₀ + T₁ + ⋯ + Tₙ`. -/
def GExpr.narySum : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.sum

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/- concordance: source L4115 EXERCISE 6.21 coalesced sum and smash -/
/-- **Exercise 6.21 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁` over `{0,1}*`.** As `sumTok`, but the
improper copies `0Δ₀`, `1Δ₁` are removed (`X ≠ Δ₀`, `Y ≠ Δ₁`), so the two bottoms are identified. -/
def oplusTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]
        exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₀.sub_master hX) hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]
        exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_mem_embF {X : Set Str} (hX : D₀.mem X) (hXne : X ≠ D₀.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) (hYne : Y ≠ D₁.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_nonempty : ∀ W, (oplusTok D₀ D₁ h₀ h₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **coalesced sum object** `𝒟₀ ⊕ 𝒟₁`. -/
def ScottSys.oplus (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨oplusTok A₀.sys A₁.sys A₀.ne A₁.ne, oplusTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- n-ary coalesced sum `T₀ ⊕ T₁ ⊕ ⋯ ⊕ Tₙ`. -/
def GExpr.naryOplus : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.oplus

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **`f₀ ⊕ f₁`, the action of the coalesced sum on maps.** -/
def oplusMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.oplus A₁).sys (B₀.oplus B₁).sys where
  rel W W' :=
    ((A₀.oplus A₁).sys.mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ X ≠ A₀.sys.master ∧ X' ≠ B₀.sys.master ∧
      W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ Y ≠ A₁.sys.master ∧ Y' ≠ B₁.sys.master ∧
      W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, hXne, -, rfl, -⟩ | ⟨Y, Y', hrel, hYne, -, rfl, -⟩)
    · exact hW
    · exact oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hrel) hXne
    · exact oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hrel) hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, hX'ne, -, rfl⟩ | ⟨Y, Y', hrel, -, hY'ne, -, rfl⟩)
    · exact Or.inl rfl
    · exact oplusTok_mem_embF (h₀ := B₀.ne) (h₁ := B₁.ne) (f₀.rel_cod hrel) hX'ne
    · exact oplusTok_mem_embT (h₀ := B₀.ne) (h₁ := B₁.ne) (f₁.rel_cod hrel) hY'ne
  master_rel := Or.inl ⟨(A₀.oplus A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, hWeq, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, hWeq,
          by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, hWeq,
          by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hX₂ne, hX'₂ne, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, -, -, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, hXne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hrel)) hX'ne, rfl,
          embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, -, -, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hY₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, hYne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hrel)) hY'ne, rfl,
          embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.oplus B₁).sys.sub_master hZ') hZZ'⟩
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃,
            hX₂ne, hX₃ne, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃,
            hY₂ne, hY₃ne, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.21 — the smash product system `𝒟₀ ⊗ 𝒟₁` over `{0,1}*`.** As `prodTok`, but proper
rectangles must avoid both top coordinates (`X ≠ Δ₀`, `Y ≠ Δ₁`); the full top `M = prodTokNbhd Δ₀ Δ₁`
is kept as the master. -/
def otimesTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := W = prodTokNbhd D₀.master D₁.master ∨
    (∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ X ≠ D₀.master ∧ Y ≠ D₁.master ∧ W = prodTokNbhd X Y)
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact subset_rfl
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
          Set.inter_eq_right.mpr (D₁.sub_master hY')]
        exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
          Set.inter_eq_right.mpr (D₁.sub_master hY)]
        exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · rw [prodTokNbhd_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, Z₁, hZ₀, hZ₁, -, -, rfl⟩
        · obtain ⟨hsub₀, -⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact absurd (Set.Subset.antisymm (D₀.sub_master hX)
            (hsub₀.trans Set.inter_subset_left)) hXne
        · obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact Or.inr ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀,
            D₁.inter_mem hY hY' hZ₁ hsub₁, inter_ne_of_ne_left (D₀.sub_master hX) hXne,
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem otimesTok_mem_master : (otimesTok D₀ D₁).mem (prodTokNbhd D₀.master D₁.master) := Or.inl rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem otimesTok_mem_prod {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y)
    (hXne : X ≠ D₀.master) (hYne : Y ≠ D₁.master) :
    (otimesTok D₀ D₁).mem (prodTokNbhd X Y) := Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem otimesTok_nonempty : ∀ W, (otimesTok D₀ D₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, Y, -, -, -, -, rfl⟩) <;> exact ⟨[], mem_prodTokNbhd_nil⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **smash product object** `𝒟₀ ⊗ 𝒟₁`. -/
def ScottSys.otimes (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨otimesTok A₀.sys A₁.sys, otimesTok_nonempty⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** -/
def GExpr.RootedConst : GExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst
  | .oplus a b => a.RootedConst ∧ b.RootedConst
  | .otimes a b => a.RootedConst ∧ b.RootedConst

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **The token-level master recursion for `GExpr`.** All four binary operations share the same body
(`sumTokMaster = prodTokNbhd` on masters). -/
def gFun : GExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .prod a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .oplus a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .otimes a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- The **Kleene iteration** `gFunⁿ({Λ})`. -/
def gIter (T : GExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => gFun T (gIter T n)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- n-ary smash product `T₀ ⊗ T₁ ⊗ ⋯ ⊗ Tₙ`. -/
def GExpr.naryOtimes : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.otimes

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **The action of `T` on objects.** -/
def GExpr.obj : GExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum a b, X => (a.obj X).sum (b.obj X)
  | .prod a b, X => (a.obj X).prod (b.obj X)
  | .oplus a b, X => (a.obj X).oplus (b.obj X)
  | .otimes a b, X => (a.obj X).otimes (b.obj X)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **`f₀ ⊗ f₁`, the action of the smash product on maps.** -/
def otimesMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.otimes A₁).sys (B₀.otimes B₁).sys where
  rel W W' :=
    ((A₀.otimes A₁).sys.mem W ∧ W' = prodTokNbhd B₀.sys.master B₁.sys.master) ∨
    (∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧ X ≠ A₀.sys.master ∧ Y ≠ A₁.sys.master ∧
      X' ≠ B₀.sys.master ∧ Y' ≠ B₁.sys.master ∧ W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, Y, X', Y', h0, h1, hXne, hYne, -, -, rfl, -⟩)
    · exact hW
    · exact otimesTok_mem_prod (f₀.rel_dom h0) (f₁.rel_dom h1) hXne hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, Y, X', Y', h0, h1, -, -, hX'ne, hY'ne, -, rfl⟩)
    · exact otimesTok_mem_master
    · exact otimesTok_mem_prod (f₀.rel_cod h0) (f₁.rel_cod h1) hX'ne hY'ne
  master_rel := Or.inl ⟨(A₀.otimes A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, ?_⟩
        rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, Y₂, X'₂, Y'₂, hr0₂, hr1₂, hX₂ne, hY₂ne, hX'₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, ?_⟩
        rw [Set.inter_comm, prodTokNbhd_inter,
          Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
        refine Or.inr ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right hr0 hr0₂,
          f₁.inter_right hr1 hr1₂, hXne, hYne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hr0)) hX'ne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hr1)) hY'ne, rfl, ?_⟩
        rw [prodTokNbhd_inter]
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((B₀.otimes B₁).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZmem with rfl | ⟨Xz, Yz, hXz, hYz, hXzne, hYzne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hWW
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master (f₀.rel_dom hr0)) hsubX) hXne
      · rcases hZ'mem with rfl | ⟨Xz', Yz', hXz', hYz', hXz'ne, hYz'ne, rfl⟩
        · exact Or.inl ⟨otimesTok_mem_prod hXz hYz hXzne hYzne, rfl⟩
        · obtain ⟨hXzX, hYzY⟩ := prodTokNbhd_subset_iff.mp hWW
          obtain ⟨hX'Xz', hY'Yz'⟩ := prodTokNbhd_subset_iff.mp hZZ'
          exact Or.inr ⟨Xz, Yz, Xz', Yz', f₀.mono hr0 hXzX hX'Xz' hXz hXz',
            f₁.mono hr1 hYzY hY'Yz' hYz hYz', hXzne, hYzne, hXz'ne, hYz'ne, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **The action of `T` on maps.** -/
def GExpr.map : (T : GExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum a b, _, _, f => sumMapTok (a.map f) (b.map f)
  | .prod a b, _, _, f => prodMapTok (a.map f) (b.map f)
  | .oplus a b, _, _, f => oplusMapTok (a.map f) (b.map f)
  | .otimes a b, _, _, f => otimesMapTok (a.map f) (b.map f)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}


/-- `gFun T Γ = tok(T({Γ}))`. -/
theorem gFun_eq_master : (T : GExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    gFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .prod a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .oplus a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .otimes a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]

/-- **`λΓ. tok(T({Γ}))` is monotone.** -/
theorem gFun_mono (T : GExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : gFun T Γ ⊆ gFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | oplus a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | otimes a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-- **`λΓ. tok(T({Γ}))` is continuous on `{Γ ∣ Λ ∈ Γ}`.** -/
theorem gFun_continuous (T : GExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ gFun T U ↔ ∃ Γ ∈ ℱ, w ∈ gFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | oplus a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | otimes a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w


theorem gFun_nil_mem : ∀ (T : GExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ gFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _
  | .oplus _ _, _, _, _ => Set.mem_insert _ _
  | .otimes _ _, _, _, _ => Set.mem_insert _ _


theorem nil_mem_gIter (T : GExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ gIter T n
  | 0 => rfl
  | n + 1 => gFun_nil_mem T hT (nil_mem_gIter T hT n)

theorem gIter_mono_step (T : GExpr) (hT : T.RootedConst) :
    ∀ n, gIter T n ⊆ gIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact gFun_nil_mem T hT rfl
  | n + 1 => gFun_mono T (gIter_mono_step T hT n)

theorem gIter_mono (T : GExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    gIter T m ⊆ gIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact gIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem gFun_iter_fixed (T : GExpr) (hT : T.RootedConst) :
    gFun T (⋃ n, gIter T n) = ⋃ n, gIter T n := by
  have hstep := gIter_mono_step T hT
  have hne : (Set.range (gIter T)).Nonempty := ⟨gIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (gIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨gIter T (max i j), ⟨max i j, rfl⟩,
      gIter_mono T hT (le_max_left i j), gIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, gIter T n) ↔ ∃ S ∈ Set.range (gIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨gIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [gFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨gIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **Exercise 6.21/6.20 (token level).** For any `GExpr` `T` whose constants contain `Λ`, there is a
set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem gExists_tok_fixedPoint (T : GExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ gFun T Γ = Γ :=
  ⟨⋃ n, gIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_gIter T hT 0⟩, gFun_iter_fixed T hT⟩

/-- **Exercise 6.21/6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies** for any construct
`T` built from constants, identity, `+`, `×`, `⊕`, `⊗`. -/
theorem gExists_singleton_subsystem (T : GExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := gExists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (gFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · exact hmaster.symm
  · intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]


end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_621 : And
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
        @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
        @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
          (T.obj (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys)
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str) Γ (@List.nil Bool))
          (@Eq (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.Exercise619.gFun T Γ) Γ)) :=
  @And.intro
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
        @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
        @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
          (T.obj (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys)
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str) Γ (@List.nil Bool))
          (@Eq (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.Exercise619.gFun T Γ) Γ))
  DomainTheory.NeighbourhoodSystems.Exercise619.gExists_singleton_subsystem
  DomainTheory.NeighbourhoodSystems.Exercise619.gExists_tok_fixedPoint
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- The `Λ ∈ tok` side-condition is preserved by any n-ary fold whose binary operation preserves it
(all four of `+`, `×`, `⊕`, `⊗` do, definitionally). -/
theorem GExpr.naryOp_rootedConst {op : GExpr → GExpr → GExpr}
    (hop : ∀ x y, (op x y).RootedConst ↔ x.RootedConst ∧ y.RootedConst) :
    ∀ (a : GExpr) (l : List GExpr), a.RootedConst → (∀ b ∈ l, b.RootedConst) →
      (GExpr.naryOp op a l).RootedConst
  | a, [], ha, _ => ha
  | a, b :: l, ha, hl => by
      rw [GExpr.naryOp, hop]
      exact ⟨ha, GExpr.naryOp_rootedConst hop b l (hl b (List.mem_cons_self ..))
        (fun c hc => hl c (List.mem_cons_of_mem _ hc))⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


theorem inter_ne_of_ne_right {X X' Δ : Set Str} (hX' : X' ⊆ Δ) (hne : X' ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX' (by rw [← h]; exact Set.inter_subset_right))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


theorem naryOplus_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryOplus a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


theorem naryOtimes_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryOtimes a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


theorem naryProd_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryProd a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **Every n-ary construct has a solution `Γ = tok(T({Γ}))`** (so `{Γ} ◁ T({Γ})` and 6.14 applies),
illustrated for the n-ary separated sum; identical for `naryProd`/`naryOplus`/`naryOtimes`. -/
theorem narySum_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.narySum a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(g₀ ∘ f₀) ⊕ (g₁ ∘ f₁) = (g₀ ⊕ g₁) ∘ (f₀ ⊕ f₁)`** for **strict** `g₀, g₁`. (Strictness of the
outer maps is exactly what prevents an intermediate top `f₀(X) = Δ₀'` from being re-expanded — that
is the categorical reason `⊕` is a functor only on the strict-map category Scott restricts to.) -/
theorem oplusMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    oplusMapTok (g₀.comp f₀) (g₁.comp f₁) = (oplusMapTok g₀ g₁).comp (oplusMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩ |
      ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.oplus B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg))
      exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, hX'ne, hX''ne, rfl, rfl⟩)⟩
    · have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg))
      exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, hY'ne, hY''ne, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, -, -, heq, -⟩ | ⟨Y, Y', -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, hX''ne, heq, rfl⟩ | ⟨Y₂, Y'', hg, -, -, heq, -⟩
      · exact Or.inl ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hf) hXne, rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, -, heq, -⟩ | ⟨Y₂, Y'', hg, -, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hf) hYne, rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(I ⊕ I) = I`.** -/
theorem oplusMapTok_id :
    oplusMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.oplus A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hsub⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, (A₀.oplus A₁).sys.sub_master hW⟩
    · exact ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX hXne,
        oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX' hX'ne, embBit_subset.mpr hsub⟩
    · exact ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY hYne,
        oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY' hY'ne, embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`oplusMapTok` is always strict.** -/
theorem oplusMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (oplusMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, -, -, heq, -⟩ | ⟨Y0, Y', -, -, -, heq, -⟩)
  · rfl
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit false X := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit true Y0 := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- `oplusMapTok` is monotone in both arguments. -/
theorem oplusMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    oplusMapTok f₀ f₁ ≤ oplusMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ |
    ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, hXne, hX'ne, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


theorem oplusTok_mem_embF_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit false W)) :
    D₀.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX
  · exact absurd heq.symm (embBit_ne (show (true : Bool) ≠ false by decide) (h₁ Y hY))

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


theorem oplusTok_mem_embT_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


theorem oplusTok_mem_master : (oplusTok D₀ D₁ h₀ h₁).mem (sumTokMaster D₀ D₁) := Or.inl rfl

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The coalesced sum carries the subsystem relation componentwise. -/
theorem oplusTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.oplus A₁).sys ◁ (B₀.oplus B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, h0.master_eq ▸ hXne, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, h1.master_eq ▸ hYne, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (oplusTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne, rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (oplusTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(g₀ ∘ f₀) ⊗ (g₁ ∘ f₁) = (g₀ ⊗ g₁) ∘ (f₀ ⊗ f₁)`** for **strict** `g₀, g₁`. -/
theorem otimesMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    otimesMapTok (g₀.comp f₀) (g₁.comp f₁) = (otimesMapTok g₀ g₁).comp (otimesMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
      hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩)
    · exact ⟨prodTokNbhd B₀.sys.master B₁.sys.master, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.otimes B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg0))
      have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg1))
      exact ⟨prodTokNbhd X' Y',
        Or.inr ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩,
        Or.inr ⟨X', Y', X'', Y'', hg0, hg1, hX'ne, hY'ne, hX''ne, hY''ne, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨Xg, Yg, X'', Y'', -, -, hXgne, -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · have heq' : prodTokNbhd B₀.sys.master B₁.sys.master = prodTokNbhd Xg Yg := heq
        obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
        exact absurd h.symm hXgne
    · rcases hW'W'' with ⟨-, rfl⟩ |
        ⟨Xg, Yg, X'', Y'', hg0, hg1, hXgne, hYgne, hX''ne, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨otimesTok_mem_prod (f₀.rel_dom hf0) (f₁.rel_dom hf1) hXne hYne, rfl⟩
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
        exact Or.inr ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
          hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(I ⊗ I) = I`.** -/
theorem otimesMapTok_id :
    otimesMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.otimes A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X', Y', ⟨hX, hX', hsubX⟩, ⟨hY, hY', hsubY⟩,
      hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.otimes A₁).sys.master_mem, (A₀.otimes A₁).sys.sub_master hW⟩
    · exact ⟨otimesTok_mem_prod hX hY hXne hYne, otimesTok_mem_prod hX' hY' hX'ne hY'ne,
        prodTokNbhd_subset_iff.mpr ⟨hsubX, hsubY⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX') hsubX) hX'ne
      · obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** -/
theorem GExpr.map_id : (T : GExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const _, _ => rfl
  | .var, _ => rfl
  | .sum a b, X => by
      show sumMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).sum (b.obj X)).sys
      rw [a.map_id X, b.map_id X, sumMapTok_id]
  | .prod a b, X => by
      show prodMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).prod (b.obj X)).sys
      rw [a.map_id X, b.map_id X, prodMapTok_id]
  | .oplus a b, X => by
      show oplusMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).oplus (b.obj X)).sys
      rw [a.map_id X, b.map_id X, oplusMapTok_id]
  | .otimes a b, X => by
      show otimesMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).otimes (b.obj X)).sys
      rw [a.map_id X, b.map_id X, otimesMapTok_id]

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`otimesMapTok` is always strict.** -/
theorem otimesMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (otimesMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, Y0, X', Y', -, -, hXne, -, -, -, heq, -⟩)
  · rfl
  · have heq' : prodTokNbhd A₀.sys.master A₁.sys.master = prodTokNbhd X Y0 := heq
    obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
    exact absurd h.symm hXne

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **Every `T` preserves strictness.** -/
theorem GExpr.map_isStrict : (T : GExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum a b, _, _, f, _ => sumMapTok_isStrict (a.map f) (b.map f)
  | .prod a b, _, _, f, hf => prodMapTok_isStrict (a.map_isStrict f hf) (b.map_isStrict f hf)
  | .oplus a b, _, _, f, _ => oplusMapTok_isStrict (a.map f) (b.map f)
  | .otimes a b, _, _, f, _ => otimesMapTok_isStrict (a.map f) (b.map f)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)` for strict `g`.** Together with `map_id`, *these are
all functors* of the strict-map category. The strictness of `g` is needed (and only) for the
coalesced `⊕`/`⊗`, whose composition law `oplusMapTok_comp`/`otimesMapTok_comp` requires it. -/
theorem GExpr.map_comp : (T : GExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    {g : ApproximableMap Y.sys Z.sys} → IsStrict g → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _, _ => rfl
  | .sum a b, _, _, _, f, g, hg => by
      show sumMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (sumMapTok (a.map g) (b.map g)).comp (sumMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact sumMapTok_comp _ _ _ _
  | .prod a b, _, _, _, f, g, hg => by
      show prodMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (prodMapTok (a.map g) (b.map g)).comp (prodMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact prodMapTok_comp _ _ _ _
  | .oplus a b, _, _, _, f, g, hg => by
      show oplusMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (oplusMapTok (a.map g) (b.map g)).comp (oplusMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact oplusMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)
  | .otimes a b, _, _, _, f, g, hg => by
      show otimesMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (otimesMapTok (a.map g) (b.map g)).comp (otimesMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact otimesMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- `otimesMapTok` is monotone in both arguments. -/
theorem otimesMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    otimesMapTok f₀ f₁ ≤ otimesMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr ⟨X, Y, X', Y', h0 X X' hr0, h1 Y Y' hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`λf. T(f)` is monotone** (the order half of *continuous on maps*). -/
theorem GExpr.map_mono : (T : GExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum a b, _, _, _, _, h => sumMapTok_mono (a.map_mono h) (b.map_mono h)
  | .prod a b, _, _, _, _, h => prodMapTok_mono (a.map_mono h) (b.map_mono h)
  | .oplus a b, _, _, _, _, h => oplusMapTok_mono (a.map_mono h) (b.map_mono h)
  | .otimes a b, _, _, _, _, h => otimesMapTok_mono (a.map_mono h) (b.map_mono h)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- Forward direction of continuity on maps for `GExpr`. -/
theorem GExpr.map_continuous_mp : (T : GExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj, rfl, rfl⟩
  | .oplus a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, hPne, hP'ne, rfl, rfl⟩ |
        ⟨Q, Q', hr, hQne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, hPne, hP'ne, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, hQne, hQ'ne, rfl, rfl⟩)⟩
  | .otimes a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, Q, P', Q', hr0, hr1, hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
        obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
        obtain ⟨k, hik, hjk⟩ := hdir i j
        exact ⟨k, Or.inr ⟨P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj,
          hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`λf. T(f)` is continuous on maps.** -/
theorem GExpr.map_continuous (T : GExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


theorem otimesTok_mem_prod_inv {X Y : Set Str} (h : (otimesTok D₀ D₁).mem (prodTokNbhd X Y))
    (hX : X ≠ D₀.master) : D₀.mem X ∧ D₁.mem Y := by
  rcases h with heq | ⟨X', Y', hX', hY', -, -, heq⟩
  · obtain ⟨rfl, -⟩ := prodTokNbhd_injective heq; exact absurd rfl hX
  · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq; exact ⟨hX', hY'⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The smash product carries the subsystem relation componentwise. -/
theorem otimesTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.otimes A₁).sys ◁ (B₀.otimes B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr ⟨X, Y, h0.sub hX, h1.sub hY, h0.master_eq ▸ hXne, h1.master_eq ▸ hYne, rfl⟩
  · rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX'),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      have hXne' : X ∩ X' ≠ B₀.sys.master := by
        rw [← h0.master_eq]; exact inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne
      obtain ⟨hmemX, hmemY⟩ := otimesTok_mem_prod_inv hInt hXne'
      exact Or.inr ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hmemX, h1.inter_closed hY hY' hmemY,
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne,
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`λX. T(X)` is monotone on domains.** -/
theorem GExpr.obj_subsystem : (T : GExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum a b, _, _, h => sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .prod a b, _, _, h => prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .oplus a b, _, _, h => oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .otimes a b, _, _, h => otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- Forward direction of continuity on domains for `GExpr`. -/
theorem GExpr.obj_continuous_mp : (T : GExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.sum a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (a.obj_subsystem hr1).sub hXD, (b.obj_subsystem hr2).sub hYD, rfl⟩
  | .oplus a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.oplus a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        refine ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, ?_, rfl⟩)⟩
        exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D hD)).master_eq)
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        refine ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, ?_, rfl⟩)⟩
        exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D hD)).master_eq)
  | .otimes a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.otimes a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
        refine ⟨D₃, hD₃, Or.inr ⟨X, Y, (a.obj_subsystem hr1).sub hXD,
          (b.obj_subsystem hr2).sub hYD, ?_, ?_, rfl⟩⟩
        · exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D₃ hD₃)).master_eq)
        · exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D₃ hD₃)).master_eq)

end Exercise619
end

section
namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`λD. T(D)` is continuous on domains.** -/
theorem GExpr.obj_continuous (T : GExpr) {ℱ : Set ScottSys} {U : ScottSys}
    (hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ) (hne : ℱ.Nonempty)
    (hsub : ∀ D ∈ ℱ, D.sys ◁ U.sys) (hU : ∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X)
    (W : Set Str) : (T.obj U).sys.mem W ↔ ∃ D ∈ ℱ, (T.obj D).sys.mem W := by
  refine ⟨T.obj_continuous_mp hdir hne hsub hU, ?_⟩
  rintro ⟨D, hD, hmem⟩
  exact (T.obj_subsystem (hsub D hD)).sub hmem

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
end

section
/- concordance: source L4127 EXERCISE 6.22 equations for the integers -/
-- Exercise622/Cnat.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- **The two-point generator `{{0},{0,Λ}}`.** Its tokens are `Δ = {0,Λ}`, with the one proper
neighbourhood `{0}` sitting strictly below the master `{0,Λ} = Δ`. As a domain this is the chain
`{0} ⊏ Δ` (one point above the bottom). Here `0 = [false]` and `Λ = []`. -/
def Cnat : ScottSys where
  sys :=
    { mem := fun X => X = {([false] : Str)} ∨ X = {([false] : Str), ([] : Str)}
      master := {([false] : Str), ([] : Str)}
      master_nonempty := ⟨[false], Set.mem_insert _ _⟩
      master_mem := Or.inr rfl
      inter_mem := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
        · exact Or.inl (Set.inter_self _)
        · exact Or.inl (Set.inter_eq_self_of_subset_left hAB)
        · exact Or.inl (Set.inter_eq_self_of_subset_right hAB)
        · exact Or.inr (Set.inter_self _)
      sub_master := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X (rfl | rfl)
        · exact hAB
        · exact subset_rfl }
  ne := by
    rintro X (rfl | rfl)
    · exact ⟨[false], rfl⟩
    · exact ⟨[false], Set.mem_insert _ _⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

section
namespace Exercise619

/-- **The one-point domain `{{Λ}} = 𝟙`** (the terminal object of Scott's category). -/
def Cone : ScottSys := singletonSys ({([] : Str)} : Set Str) ⟨[], rfl⟩

end Exercise619
end

section
namespace Exercise619

/-- `T(X) = {{Λ}} + X` — the right-hand side of `M ≅ {{Λ}} + M`. -/
def MExpr : GExpr := .sum (.const Cone) .var

end Exercise619
end

section
namespace Exercise619

/-- `T(X) = {{0},{0,Λ}} ⊕ X` — the right-hand side of `N ≅ {{0},{0,Λ}} ⊕ N`. -/
def NExpr : GExpr := .oplus (.const Cnat) .var

end Exercise619
end

section
namespace Exercise619

/-- `T(X) = N ⊕ (N ⊗ X)` — the right-hand side of `N* ≅ N ⊕ (N ⊗ N*)`, parametrised by the (rooted)
datum domain `N`. -/
def NStarExpr (N : ScottSys) : GExpr := .oplus (.const N) (.otimes (.const N) .var)

end Exercise619
end

section
namespace Exercise619


theorem NStarExpr_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) :
    (NStarExpr N).RootedConst := ⟨hN, hN, trivial⟩

end Exercise619
end

section
namespace Exercise619


/-- **`N* ≅ N ⊕ (N ⊗ N*)` has a solution** for any rooted datum domain `N` (the strict streams over
`N`). -/
theorem NStar_eq_solution (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem (NStarExpr N) (NStarExpr_rooted hN)

end Exercise619
end

section
namespace Exercise619


/-- `Λ ∈ tok(Cnat)`, so `Cnat` is a rooted constant. -/
theorem nil_mem_Cnat : ([] : Str) ∈ Cnat.sys.master := Set.mem_insert_iff.mpr (Or.inr rfl)

end Exercise619
end

section
namespace Exercise619


theorem NExpr_rooted : NExpr.RootedConst := ⟨nil_mem_Cnat, trivial⟩

end Exercise619
end

section
namespace Exercise619


/-- **Chaining the equations.** The solution `N` to the first equation is itself a rooted domain
(`Λ ∈ tok(N)`, since its token set is the fixed point `Γ₁ ∋ Λ`), so it is a legitimate datum domain
for the third: `N*` exists *over the very `N` produced by* `N ≅ {{0},{0,Λ}} ⊕ N`. -/
theorem NStar_over_N_exists :
    ∃ N : ScottSys, ([] : Str) ∈ N.sys.master ∧
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ₁, hnil₁, _⟩ := gExists_tok_fixedPoint NExpr NExpr_rooted
  exact ⟨singletonSys Γ₁ ⟨[], hnil₁⟩, hnil₁, NStar_eq_solution _ hnil₁⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_622 : ∃ (N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
    (∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
      @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
      @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
        ((DomainTheory.NeighbourhoodSystems.Exercise619.NStarExpr N).obj
            (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise619.NStar_over_N_exists
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- **`N ≅ {{0},{0,Λ}} ⊕ N` has a solution.** There is `Γ` (the vertical naturals' token set) with
`Γ = tok(NExpr({Γ}))`, so `{Γ} ◁ NExpr({Γ})` and Theorem 6.14 applies. -/
theorem N_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (NExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem NExpr NExpr_rooted

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- `Λ ∈ tok(Cone)`. -/
theorem nil_mem_Cone : ([] : Str) ∈ Cone.sys.master := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


theorem MExpr_rooted : MExpr.RootedConst := ⟨nil_mem_Cone, trivial⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- **`M ≅ {{Λ}} + M` has a solution** (the lazy naturals). -/
theorem M_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (MExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem MExpr MExpr_rooted

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The fixed-point token set `Γ = tok(T({Γ}))`**, as the explicit Kleene union `⋃ₙ gIter T n`
(no `Classical.choice`). -/
def gFix (T : GExpr) : Set Str := ⋃ n, gIter T n

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- `Γ = tok(T({Γ}))` at the token level: `gFun T Γ = Γ`. -/
theorem gFix_fixed (T : GExpr) (hT : T.RootedConst) : gFun T (gFix T) = gFix T :=
  gFun_iter_fixed T hT

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem gFix_nil_mem (T : GExpr) : ([] : Str) ∈ gFix T :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem gFix_nonempty (T : GExpr) : (gFix T).Nonempty := ⟨[], gFix_nil_mem T⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The one-point generator `{Γ}`** as an object of the category. -/
def gGen (T : GExpr) : ScottSys := singletonSys (gFix T) (gFix_nonempty T)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gGen_master (T : GExpr) : (gGen T).sys.master = gFix T := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **`{Γ} ◁ T({Γ})`** — Scott's hypothesis for Theorem 6.14, the base of the tower. (This is the
content of `gExists_singleton_subsystem`, here at the *explicit* generator `Γ = gFix T`.) -/
theorem gBase (T : GExpr) (hT : T.RootedConst) : (gGen T).sys ◁ (T.obj (gGen T)).sys := by
  have hmaster : (T.obj (gGen T)).sys.master = gFix T :=
    (gFun_eq_master T (gFix_nonempty T)).symm.trans (gFix_fixed T hT)
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have heq : X = (T.obj (gGen T)).sys.master := (hX : X = gFix T).trans hmaster.symm
    rw [heq]; exact (T.obj (gGen T)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = gFix T
    rw [show X = gFix T from hX, show Y = gFix T from hY, Set.inter_self]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The tower `Tⁿ({Γ})`** of `∅`-free systems over `Str`: `T⁰({Γ}) = {Γ}`, `Tⁿ⁺¹({Γ}) =
T(Tⁿ({Γ}))`. -/
def gTower (T : GExpr) : ℕ → ScottSys
  | 0 => gGen T
  | n + 1 => T.obj (gTower T n)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gTower_zero (T : GExpr) : gTower T 0 = gGen T := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gTower_succ (T : GExpr) (n : ℕ) : gTower T (n + 1) = T.obj (gTower T n) := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The basic chain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`.** Base: `gBase`. Step: `T` is monotone on domains
(`obj_subsystem`). -/
theorem gChain (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys ◁ (gTower T (n + 1)).sys
  | 0 => gBase T hT
  | n + 1 => T.obj_subsystem (gChain T hT n)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem gTower_le (T : GExpr) (hT : T.RootedConst) {n m : ℕ} (h : n ≤ m) :
    (gTower T n).sys ◁ (gTower T m).sys := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (gChain T hT _)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- Every level of the tower has the same master `Δ = Γ`. -/
theorem gTower_master (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys.master = gFix T
  | 0 => rfl
  | n + 1 => ((gChain T hT n).master_eq).symm.trans (gTower_master T hT n)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The colimit system `𝒟 = ⋃ₙ Tⁿ({Γ})`** as an `∅`-free system over `Str`. A set is a
neighbourhood exactly when it is a neighbourhood of some level; closure under consistent intersection
uses that the tower is a chain (any finite collection sits inside one level). -/
def gColim (T : GExpr) (hT : T.RootedConst) : ScottSys where
  sys :=
    { mem := fun X => ∃ n, (gTower T n).sys.mem X
      master := gFix T
      master_nonempty := (gTower T 0).sys.master_nonempty
      master_mem := ⟨0, (gTower T 0).sys.master_mem⟩
      inter_mem := by
        rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
        set N := max n (max m p) with hN
        have hXN : (gTower T N).sys.mem X := (gTower_le T hT (le_max_left n _)).sub hX
        have hYN : (gTower T N).sys.mem Y :=
          (gTower_le T hT ((le_max_left m p).trans (le_max_right n _))).sub hY
        have hZN : (gTower T N).sys.mem Z :=
          (gTower_le T hT ((le_max_right m p).trans (le_max_right n _))).sub hZ
        exact ⟨N, (gTower T N).sys.inter_mem hXN hYN hZN hsub⟩
      sub_master := by
        rintro X ⟨n, hX⟩
        rw [← gTower_master T hT n]
        exact (gTower T n).sys.sub_master hX }
  ne := by rintro X ⟨n, hX⟩; exact (gTower T n).ne X hX

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem mem_gColim (T : GExpr) (hT : T.RootedConst) {X : Set Str} :
    (gColim T hT).sys.mem X ↔ ∃ n, (gTower T n).sys.mem X := Iff.rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gColim_master (T : GExpr) (hT : T.RootedConst) :
    (gColim T hT).sys.master = gFix T := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The functor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23, as a `GExpr` over the variable
domain `N`. The `⊕ N` carries the variables, and the two `(X×X)` summands (combined by `+`) carry the
two binary operation symbols. -/
def Texp (N : ScottSys) : GExpr :=
  .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- `Texp N` is rooted iff the variable domain `N` is (`Λ ∈ tok(N)`, automatic for the fixed-point
solutions of 6.19–6.22). -/
theorem Texp_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) : (Texp N).RootedConst :=
  ⟨hN, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The syntactic domain of expressions** `Exp = ⋃ₙ Texpⁿ({Γ})`, the initial solution of
`Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`. -/
def Exp (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : ScottSys :=
  gColim (Texp N) (Texp_rooted hN)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- Two objects of the category with the same underlying system are equal (the `∅`-freeness field is
a `Prop`). -/
theorem ScottSys.ext {A B : ScottSys} (h : A.sys = B.sys) : A = B := by
  cases A; cases B; cases h; rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The category of `∅`-free domains over `Str` and strict maps.** Morphisms are strict approximable
maps (`StrictMap`); identities and associative composition are Theorem 2.5, with strictness preserved
by `isStrict_idMap`/`isStrict_comp`. The fixed carrier `Str` is what removes all the carrier-transport
`HEq` that burdens the abstract `Endofunctor DomainObj`. -/
instance : Category ScottSys where
  Hom A B := StrictMap A.sys B.sys
  id A := ⟨idMap A.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (comp_idMap f.1)
  comp_id f := Subtype.ext (idMap_comp f.1)
  assoc f g h := Subtype.ext (comp_assoc h.1 g.1 f.1).symm

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem gTower_sub_colim (T : GExpr) (hT : T.RootedConst) (n : ℕ) :
    (gTower T n).sys ◁ (gColim T hT).sys where
  master_eq := by rw [gColim_master, gTower_master T hT]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (gTower T (max n m)).sys.mem (X ∩ Y) :=
      (gTower_le T hT (le_max_right n m)).sub hXY
    exact (gTower_le T hT (le_max_left n m)).inter_closed hX hY hN

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **`T(𝒟) = 𝒟` at the level of neighbourhood systems.** Membership: continuity on domains
(`obj_continuous`) along the directed tower turns `T(⋃ₙ Tⁿ({Γ}))` into `⋃ₙ Tⁿ⁺¹({Γ})`, which has the
same neighbourhoods as `⋃ₙ Tⁿ({Γ})` (the extra `n=0` level `T⁰({Γ})` is absorbed by the chain step).
Master: both are `Γ` (`gTower_master` through `obj_subsystem` of `Tⁿ({Γ}) ◁ 𝒟`). -/
theorem gColim_obj_sys_eq (T : GExpr) (hT : T.RootedConst) :
    (T.obj (gColim T hT)).sys = (gColim T hT).sys := by
  set ℱ : Set ScottSys := Set.range (gTower T) with hℱ
  have hne : ℱ.Nonempty := ⟨gTower T 0, 0, rfl⟩
  have hsub : ∀ D ∈ ℱ, D.sys ◁ (gColim T hT).sys := by
    rintro D ⟨n, rfl⟩; exact gTower_sub_colim T hT n
  have hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨gTower T (max n m), ⟨max n m, rfl⟩,
      gTower_le T hT (le_max_left n m), gTower_le T hT (le_max_right n m)⟩
  have hU : ∀ X, (gColim T hT).sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X := by
    intro X; constructor
    · rintro ⟨n, hn⟩; exact ⟨gTower T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  apply NeighborhoodSystem.ext
  · intro W
    rw [T.obj_continuous hdir hne hsub hU W]
    constructor
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩
      -- `T(Tⁿ({Γ})) = Tⁿ⁺¹({Γ})`, a level of the colimit.
      exact ⟨n + 1, hn⟩
    · rintro ⟨n, hn⟩
      -- a colimit neighbourhood at level `n` is, after one chain step, at `T(Tⁿ({Γ}))`.
      exact ⟨gTower T n, ⟨n, rfl⟩, (gChain T hT n).sub hn⟩
  · -- masters: `(T 𝒟).master = (Tⁿ⁺¹({Γ})).master = Γ = 𝒟.master`, via `obj_subsystem` at `n=0`.
    have h := (T.obj_subsystem (gTower_sub_colim T hT 0)).master_eq
    rw [gColim_master]
    rw [show (T.obj (gTower T 0)) = gTower T 1 from rfl] at h
    rw [← h, gTower_master T hT]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The structure isomorphism `T(𝒟) ≅ 𝒟` is the identity** (the two objects are literally equal). -/
theorem gColim_obj_eq (T : GExpr) (hT : T.RootedConst) : T.obj (gColim T hT) = gColim T hT :=
  ScottSys.ext (gColim_obj_sys_eq T hT)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The domain equation `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`**, realised as an equality of systems
(the structure map is the identity). This is the "construe the initial solution" half of
Exercise 6.23. -/
theorem Exp_structure_eq (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (Texp N).obj (Exp N hN) = Exp N hN :=
  gColim_obj_eq (Texp N) (Texp_rooted hN)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem ScottSys.id_val (A : ScottSys) :
    ((𝟙 A) : StrictMap A.sys A.sys).1 = idMap A.sys := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem ScottSys.comp_val {A B C : ScottSys} (g : (B ⟶ C)) (f : (A ⟶ B)) :
    ((g ⊚ f : StrictMap A.sys C.sys)).1 = g.1.comp f.1 := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The morphism action of `gFunctor T`: a strict `f` is sent to the strict map `T(f)`. (Typed via
`StrictMap`, which is defeq to the category's `Hom`; this avoids the class-projection that blocks the
anonymous `.1` on `Category.Hom`.) -/
def gFunctorMap (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    StrictMap (T.obj X).sys (T.obj Y).sys :=
  ⟨T.map f.1, T.map_isStrict f.1 f.2⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **Every `GExpr` is an `Endofunctor` of the strict-map category.** On objects it is `GExpr.obj`;
on a strict map `f` it is the strict map `T(f)` (`GExpr.map_isStrict`). Functoriality is
`GExpr.map_id` and `GExpr.map_comp` (the latter needs `g` strict — automatic here, since every
morphism of this category is strict). -/
abbrev gFunctor (T : GExpr) : Endofunctor ScottSys where
  obj := T.obj
  map := gFunctorMap T
  map_id X := Subtype.ext (T.map_id X)
  map_comp {_ _ _} g f :=
    Subtype.ext (T.map_comp (f : StrictMap _ _).1 (g : StrictMap _ _).2)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gFunctor_obj (T : GExpr) (X : ScottSys) : (gFunctor T).obj X = T.obj X := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

@[simp] theorem gFunctorMap_val (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    (gFunctorMap T f).1 = T.map f.1 := rfl

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The endofunctor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23. -/
abbrev TexpF (N : ScottSys) : Endofunctor ScottSys := gFunctor (Texp N)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The structure map of an algebra `B`, as a raw approximable map (its strictness is `algStr_strict`).
The ascription to `StrictMap` forces the categorical `Hom` to its underlying subtype. -/
def algStr (B : TAlgebra (TexpF N)) :
    ApproximableMap ((TexpF N).obj B.carrier).sys B.carrier.sys :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).1

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem algStr_strict (B : TAlgebra (TexpF N)) : IsStrict (algStr B) :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).2

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The identity isomorphism in any category induced by an object equality. -/
def isoOfObjEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨(𝟙 X), (𝟙 X), CategoryTheory.Category.id_comp _, CategoryTheory.Category.id_comp _⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The structure isomorphism `T(Exp) ≅ Exp`.** Since Phase 1 proved `T(Exp) = Exp` as objects
(`Exp_structure_eq`), this is the identity isomorphism. -/
def ExpIso (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    Iso ((TexpF N).obj (Exp N hN)) (Exp N hN) :=
  isoOfObjEq (Exp_structure_eq N hN)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **`Exp` as a `T`-algebra** with structure map the isomorphism `T(Exp) ≅ Exp` (the identity, since
`T(Exp) = Exp`). This realises Scott's "construe the initial solution as a syntactic domain of
expressions": `Exp` is an algebra of `T(X) = N ⊕ ((X×X)+(X×X))`. -/
abbrev ExpAlg (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : TAlgebra (TexpF N) where
  carrier := Exp N hN
  str := (ExpIso N hN).hom

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The structure map `i : T(Exp) → Exp` as a raw map (the identity, since `T(Exp) = Exp`). -/
def expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys :=
  ((ExpIso N hN).hom : StrictMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys).1

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The inverse `j = i⁻¹ : Exp → T(Exp)` of the structure isomorphism, as a raw map. -/
def expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).1

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The Kleene iterates `valₙ : Exp → D`** of the operator `λh. k ∘ T(h) ∘ j`. `val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`. -/
def descRel : ℕ → ApproximableMap (Exp N hN).sys B.carrier.sys
  | 0 => constMap (Exp N hN).sys B.carrier.sys.bot
  | n + 1 => (algStr B).comp (((Texp N).map (descRel n)).comp (expInv N hN))

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

@[simp] theorem descRel_succ (n : ℕ) :
    descRel hN B (n + 1) = (algStr B).comp (((Texp N).map (descRel hN B n)).comp (expInv N hN)) :=
  rfl

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- Two algebra homomorphisms with equal underlying maps are equal. -/
theorem algHom_ext {A C : TAlgebra (TexpF N)} {g g' : AlgHom A C} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- The constant `⊥` map is below every approximable map (it relates each domain neighbourhood only
to the codomain master, which every map produces by monotonicity from `master_rel`). -/
theorem constBot_le {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (g : ApproximableMap V₀ V₁) : constMap V₀ V₁.bot ≤ g := by
  intro X Y hr
  obtain ⟨hX, hY⟩ := hr
  rw [NeighborhoodSystem.mem_bot] at hY
  subst hY
  exact g.mono g.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- The iterates increase: `valₙ ≤ valₙ₊₁`. -/
theorem descRel_le_succ : ∀ n, descRel hN B n ≤ descRel hN B (n + 1)
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, descRel_succ]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_succ n)) le_rfl)

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- The iterates form a `≤`-chain. -/
theorem descRel_mono {i j : ℕ} (h : i ≤ j) : descRel hN B i ≤ descRel hN B j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descRel_le_succ hN B _)

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- Directedness witness for the union (any two iterates are dominated by the later one). -/
theorem descDir (i j : ℕ) : ∃ k, (∀ X Y, (descRel hN B i).rel X Y → (descRel hN B k).rel X Y) ∧
    (∀ X Y, (descRel hN B j).rel X Y → (descRel hN B k).rel X Y) :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- Directedness of the iterates in `≤`-form (for `map_continuous`). -/
theorem descDirLe (i j : ℕ) :
    ∃ k, descRel hN B i ≤ descRel hN B k ∧ descRel hN B j ≤ descRel hN B k :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The evaluation map `val = ⋃ₙ valₙ`** as an approximable map. -/
def descMap : ApproximableMap (Exp N hN).sys B.carrier.sys :=
  iSupMap (descRel hN B) (descDir hN B)

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- `val` is the relational union of the iterates (the hypothesis for `map_continuous`). -/
theorem descMap_is_sup (A E : Set Str) :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The fixed-point equation `val = k ∘ T(val) ∘ j`.** Forward: an iterate `valₙ` is, after the
recursion, `k ∘ T(valₙ₋₁) ∘ j`, and `T(valₙ₋₁) ⊆ T(val)` by continuity on maps. Backward: a witness
factoring through `T(valₙ)` lands in `valₙ₊₁`. -/
theorem descMap_fix :
    descMap hN B = (algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN)) := by
  have hmc : ∀ Y C, ((Texp N).map (descMap hN B)).rel Y C
      ↔ ∃ n, ((Texp N).map (descRel hN B n)).rel Y C :=
    fun Y C => (Texp N).map_continuous (descRel hN B) (descMap hN B) (descDirLe hN B)
      (descMap_is_sup hN B) Y C
  apply ApproximableMap.ext
  intro A E
  rw [comp_rel]
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (descRel hN B (n + 1)).rel A E := descRel_le_succ hN B n A E hn
    rw [descRel_succ, comp_rel] at hn1
    obtain ⟨C, hAC, hCE⟩ := hn1
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    exact ⟨C, ⟨Y, hAY, (hmc Y C).mpr ⟨n, hYC⟩⟩, hCE⟩
  · rintro ⟨C, hAC, hCE⟩
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    obtain ⟨n, hn⟩ := (hmc Y C).mp hYC
    refine ⟨n + 1, ?_⟩
    rw [descRel_succ, comp_rel]
    exact ⟨C, by rw [comp_rel]; exact ⟨Y, hAY, hn⟩, hCE⟩

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

theorem descMap_rel {A E : Set Str} :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- `j ∘ i = I_{T(Exp)}` at the raw level (from the iso's `hom_inv_id`). -/
theorem expInv_comp_expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expInv N hN).comp (expHom N hN) = idMap ((TexpF N).obj (Exp N hN)).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).hom_inv_id
  exact h

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The homomorphism square `val ∘ i = k ∘ T(val)`** at the raw level (conjugating the fixed-point
equation by `i`, using `j ∘ i = I`). -/
theorem descComm :
    (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B)) := by
  calc (descMap hN B).comp (expHom N hN)
      = ((algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN))).comp (expHom N hN) := by
        rw [← descMap_fix]
    _ = (algStr B).comp ((((Texp N).map (descMap hN B)).comp (expInv N hN)).comp (expHom N hN)) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp ((expInv N hN).comp (expHom N hN))) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp (idMap _)) := by
        rw [expInv_comp_expHom]
    _ = (algStr B).comp ((Texp N).map (descMap hN B)) := by rw [comp_idMap]

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

theorem expInv_strict (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : IsStrict (expInv N hN) :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).2

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- Every iterate is strict. -/
theorem descRel_isStrict : ∀ n, IsStrict (descRel hN B n)
  | 0 => isStrict_constBot
  | n + 1 => by
      rw [descRel_succ]
      exact isStrict_comp (algStr_strict B)
        (isStrict_comp ((Texp N).map_isStrict _ (descRel_isStrict n)) (expInv_strict N hN))

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- `val` is strict (a union of strict maps). -/
theorem descMap_isStrict : IsStrict (descMap hN B) := by
  rintro Y ⟨n, hn⟩
  exact descRel_isStrict hN B n hn

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The evaluation homomorphism `val(s) : Exp → D`** as a `T`-algebra homomorphism — Scott's
existence of the evaluation map. -/
def descAlgHom : AlgHom (ExpAlg N hN) B where
  hom := ⟨descMap hN B, descMap_isStrict hN B⟩
  comm := by
    apply Subtype.ext
    show (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B))
    exact descComm hN B

end Existence

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- The subdomain `Texpⁿ({Γ}) ◁ Exp` (Proposition 6.12's pair lives here). -/
theorem expSub (n : ℕ) : (gTower (Texp N) n).sys ◁ (Exp N hN).sys :=
  gTower_sub_colim (Texp N) (Texp_rooted hN) n

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- The injection `i : D → E` of a subsystem is **strict**: `i` sends `Δ_D` only to `Δ_E`. -/
theorem Subsystem.inj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.inj := by
  intro Y hrel
  rw [Subsystem.inj_rel] at hrel
  obtain ⟨_, hYE, hsub⟩ := hrel
  exact Set.Subset.antisymm (E.sub_master hYE) (by rw [← h.master_eq]; exact hsub)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The forward map of the identity iso `isoOfObjEq e` is the inclusion `X ↪ Y` (= `idMap` across the
object equality `e`). -/
theorem isoOfObjEq_hom_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).hom).1.rel A E ↔ X.sys.mem A ∧ Y.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Relational description of the structure map `i = expHom`** (the identity `T(Exp) = Exp`). -/
theorem expHom_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expHom N hN).rel A E ↔
      ((Texp N).obj (Exp N hN)).sys.mem A ∧ (Exp N hN).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_hom_rel (Exp_structure_eq N hN)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The inverse map of the identity iso `isoOfObjEq e`. -/
theorem isoOfObjEq_inv_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).inv).1.rel A E ↔ Y.sys.mem A ∧ X.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Relational description of the inverse structure map `j = expInv`**. -/
theorem expInv_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expInv N hN).rel A E ↔
      (Exp N hN).sys.mem A ∧ ((Texp N).obj (Exp N hN)).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_inv_rel (Exp_structure_eq N hN)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Coalesced sum carries the injection.** -/
theorem oplusMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.inj h1.inj = (oplusTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.oplus A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (B₀.oplus B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Coalesced sum carries the projection.** -/
theorem oplusMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.proj h1.proj = (oplusTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.oplus B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Smash product carries the injection.** -/
theorem otimesMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.inj h1.inj = (otimesTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (B₀.otimes B₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd A₀.sys.master A₁.sys.master
            = prodTokNbhd B₀.sys.master B₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨B₀.sys.sub_master (h0.sub hP),
          B₁.sys.sub_master (h1.sub hQ)⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (B₀.sys.sub_master hX')
          (by rw [← h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Smash product carries the projection.** -/
theorem otimesMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.proj h1.proj = (otimesTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (A₀.otimes A₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd B₀.sys.master B₁.sys.master
            = prodTokNbhd A₀.sys.master A₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨by rw [h0.master_eq]; exact B₀.sys.sub_master hP,
          by rw [h1.master_eq]; exact B₁.sys.sub_master hQ⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX')
          (by rw [h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Product carries the injection.** -/
theorem prodMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.inj h1.inj = (prodTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Product carries the projection.** -/
theorem prodMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.proj h1.proj = (prodTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- **`ρₙ = iₙ ∘ jₙ : Exp → Exp`**, the retraction onto `Texpⁿ({Γ})`. -/
def rho (n : ℕ) : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  (expSub hN n).inj.comp (expSub hN n).proj

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- Scott's relational description `A ρₙ E ↔ ∃ z ∈ Texpⁿ({Γ}), A ⊆ z ⊆ E`. -/
theorem rho_rel (n : ℕ) {A E : Set Str} :
    (rho hN n).rel A E ↔ (Exp N hN).sys.mem A ∧ (Exp N hN).sys.mem E ∧
      ∃ z, (gTower (Texp N) n).sys.mem z ∧ A ⊆ z ∧ z ⊆ E := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, hproj, hinj⟩
    rw [Subsystem.proj_rel] at hproj
    rw [Subsystem.inj_rel] at hinj
    obtain ⟨hcA, hTz, hAz⟩ := hproj
    obtain ⟨_, hcE, hzE⟩ := hinj
    exact ⟨hcA, hcE, z, hTz, hAz, hzE⟩
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨z, by rw [Subsystem.proj_rel]; exact ⟨hcA, hTz, hAz⟩,
      by rw [Subsystem.inj_rel]; exact ⟨hTz, hcE, hzE⟩⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- `ρₙ ⊆ ρₘ` for `n ≤ m`. -/
theorem rho_mono {n m : ℕ} (h : n ≤ m) {A E : Set Str} (hr : (rho hN n).rel A E) :
    (rho hN m).rel A E := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcA, hcE, z, hTz, hAz, hzE⟩ := hr
  exact ⟨hcA, hcE, z, (gTower_le (Texp N) (Texp_rooted hN) h).sub hTz, hAz, hzE⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- The pointwise union `⋃ₙ ρₙ`. -/
def iSupRho : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  iSupMap (rho hN) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono hN (le_max_left i j) h,
    fun _ _ h => rho_mono hN (le_max_right i j) h⟩)

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- **`⋃ₙ ρₙ = I_Exp`** (Scott's key identity). -/
theorem iSupRho_eq_id : iSupRho hN = idMap (Exp N hN).sys := by
  apply ApproximableMap.ext
  intro A E
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcA, hcE, z, _, hAz, hzE⟩ := hr
    exact ⟨hcA, hcE, hAz.trans hzE⟩
  · rintro ⟨hcA, hcE, hAE⟩
    obtain ⟨n, hA⟩ := hcA
    exact ⟨n, (rho_rel hN n).mpr ⟨⟨n, hA⟩, hcE, A, hA, subset_rfl, hAE⟩⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- **`ρ₀ = ⊥`** (the generator `{Γ}` is one-point): `ρ₀` relates `A` only to the master. -/
theorem rho_zero_rel {A E : Set Str} :
    (rho hN 0).rel A E ↔ (Exp N hN).sys.mem A ∧ E = (Exp N hN).sys.master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcA, hcE, z, hz, _, hzE⟩
    have hzm : z = (Exp N hN).sys.master :=
      (hz : z = gFix (Texp N)).trans (gColim_master (Texp N) (Texp_rooted hN)).symm
    subst hzm
    exact ⟨hcA, Set.Subset.antisymm ((Exp N hN).sys.sub_master hcE) hzE⟩
  · rintro ⟨hcA, rfl⟩
    exact ⟨hcA, (Exp N hN).sys.master_mem, (Exp N hN).sys.master,
      gColim_master (Texp N) (Texp_rooted hN), (Exp N hN).sys.sub_master hcA, subset_rfl⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- The base of the recursion: `g ∘ ρ₀ = ⊥ = val₀`, independent of `g`. -/
theorem gcomp_rho_zero (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1.comp (rho hN 0) = descRel hN B 0 := by
  apply ApproximableMap.ext
  intro A Z
  rw [comp_rel]
  constructor
  · rintro ⟨E, hrho, hg⟩
    rw [rho_zero_rel] at hrho
    obtain ⟨hcA, rfl⟩ := hrho
    have hZ : Z = B.carrier.sys.master := g.hom.2 hg
    exact ⟨hcA, by rw [NeighborhoodSystem.mem_bot]; exact hZ⟩
  · rintro ⟨hcA, hZ⟩
    rw [NeighborhoodSystem.mem_bot] at hZ
    subst hZ
    exact ⟨(Exp N hN).sys.master, (rho_zero_rel hN).mpr ⟨hcA, rfl⟩, g.hom.1.master_rel⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- On `D ◁ D` (e.g. `Subsystem.refl`), the injection is the identity (both relations are
`X ∈ D ∧ Y ∈ D ∧ X ⊆ Y`). -/
theorem Subsystem.self_inj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.inj_rel, idMap_rel]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- On `D ◁ D`, the projection is the identity. -/
theorem Subsystem.self_proj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.proj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.proj_rel, idMap_rel]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Sum carries the injection.** `(i₀ + i₁) = i` for the sum subsystem: both relate `W ↦ W'` iff
`W ∈ 𝒟₀+𝒟₁`, `W' ∈ ℰ₀+ℰ₁`, `W ⊆ W'`. -/
theorem sumMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.inj h1.inj = (sumTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.sum A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (B₀.sum B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **`T(i) = i'`** — the functor carries the injection of `D ◁ E` to that of `T(D) ◁ T(E)`. -/
theorem GExpr.map_inj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.inj = (T.obj_subsystem h).inj
  | .const D, _, _, _ => (Subsystem.self_inj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.inj) (b.map h.inj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, sumMapTok_inj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.inj) (b.map h.inj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, prodMapTok_inj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.inj) (b.map h.inj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, oplusMapTok_inj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.inj) (b.map h.inj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, otimesMapTok_inj]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Sum carries the projection.** -/
theorem sumMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.proj h1.proj = (sumTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.sum B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **`T(j) = j'`** — the functor carries the projection of `D ◁ E` to that of `T(D) ◁ T(E)`. -/
theorem GExpr.map_proj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.proj = (T.obj_subsystem h).proj
  | .const D, _, _, _ => (Subsystem.self_proj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.proj) (b.map h.proj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, sumMapTok_proj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.proj) (b.map h.proj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, prodMapTok_proj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.proj) (b.map h.proj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, oplusMapTok_proj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.proj) (b.map h.proj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, otimesMapTok_proj]

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- `T(ρₙ) = T(iₙ) ∘ T(jₙ) = i'ₙ ∘ j'ₙ`, the projection pair of `T(Texpⁿ{Γ}) ◁ T(Exp)`. -/
theorem map_rho_eq (n : ℕ) :
    (Texp N).map (rho hN n)
      = ((Texp N).obj_subsystem (expSub hN n)).inj.comp
        ((Texp N).obj_subsystem (expSub hN n)).proj := by
  unfold rho
  rw [(Texp N).map_comp (expSub hN n).proj (Subsystem.inj_isStrict (expSub hN n)),
      (Texp N).map_inj, (Texp N).map_proj]

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). -/
theorem key_rho (n : ℕ) :
    rho hN (n + 1)
      = (expHom N hN).comp (((Texp N).map (rho hN n)).comp (expInv N hN)) := by
  have hsyseq : ((Texp N).obj (Exp N hN)).sys = (Exp N hN).sys :=
    gColim_obj_sys_eq (Texp N) (Texp_rooted hN)
  apply ApproximableMap.ext
  intro A E
  rw [map_rho_eq]
  simp only [comp_rel, rho_rel, expInv_rel, expHom_rel, Subsystem.proj_rel,
    Subsystem.inj_rel, hsyseq]
  constructor
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨E, ⟨A, ⟨hcA, hcA, subset_rfl⟩, z, ⟨hcA, hTz, hAz⟩, hTz, hcE, hzE⟩,
      hcE, hcE, subset_rfl⟩
  · rintro ⟨Y, ⟨C, ⟨hcA, _, hAC⟩, z, ⟨_, hTz, hCz⟩, _, _, hzY⟩, _, hcE, hYE⟩
    exact ⟨hcA, hcE, z, hTz, hAC.trans hCz, hzY.trans hYE⟩

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`** (`key_rho` + the homomorphism square). -/
theorem gcomp_rho_succ (g : AlgHom (ExpAlg N hN) B) (n : ℕ) :
    g.hom.1.comp (rho hN (n + 1))
      = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1.comp (rho hN (n + 1))
      = g.hom.1.comp ((expHom N hN).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := by rw [key_rho]
    _ = (g.hom.1.comp (expHom N hN)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        congrArg (fun m => m.comp (((Texp N).map (rho hN n)).comp (expInv N hN))) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := comp_assoc _ _ _
    _ = (algStr B).comp ((((Texp N).map g.hom.1).comp ((Texp N).map (rho hN n))).comp
          (expInv N hN)) :=
        congrArg ((algStr B).comp ·)
          (comp_assoc ((Texp N).map g.hom.1) ((Texp N).map (rho hN n)) (expInv N hN)).symm
    _ = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) :=
        congrArg (fun m => (algStr B).comp (m.comp (expInv N hN)))
          ((Texp N).map_comp (rho hN n) g.hom.2).symm

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- **`g ∘ ρₙ = val₀ₙ`**: every homomorphism `g` agrees with the canonical Kleene iterate after the
`n`-th projection — the sequence is forced by the recursion, independent of `g`. -/
theorem gcomp_rho_eq (g : AlgHom (ExpAlg N hN) B) :
    ∀ n, g.hom.1.comp (rho hN n) = descRel hN B n
  | 0 => gcomp_rho_zero hN B g
  | n + 1 => by rw [gcomp_rho_succ hN B g n, gcomp_rho_eq g n, ← descRel_succ]

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- **The underlying map of any homomorphism `g : Exp → D` is `val = descMap`.** Hence `descAlgHom`
is the *unique* homomorphism. -/
theorem descMap_eq_algHom (g : AlgHom (ExpAlg N hN) B) : g.hom.1 = descMap hN B := by
  have hcomp : g.hom.1.comp (iSupRho hN) = descMap hN B := by
    apply ApproximableMap.ext
    intro A E
    rw [comp_rel, descMap_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hg⟩
      refine ⟨n, ?_⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel]
      exact ⟨Y, hrho, hg⟩
    · rintro ⟨n, hn⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel] at hn
      obtain ⟨Y, hrho, hg⟩ := hn
      exact ⟨Y, ⟨n, hrho⟩, hg⟩
  calc g.hom.1 = g.hom.1.comp (iSupRho hN) := by
        rw [iSupRho_eq_id hN]; exact (comp_idMap g.hom.1).symm
    _ = descMap hN B := hcomp

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/- concordance: source L4141 EXERCISE 6.23 syntactic expression domain -/
/-- **Exercise 6.23 (Scott 1981, PRG-19) — `Exp` is the initial `T`-algebra.** For every algebra
`B = (D, s, u, v)` there is a *unique* homomorphism `val(s) : Exp → D` — Scott's evaluation of an
expression. Existence is `descAlgHom` (Phase 3); uniqueness is the projection-chain argument. -/
def ExpInitial : IsInitial (ExpAlg N hN) where
  desc B := descAlgHom hN B
  uniq B g := algHom_ext (Subtype.ext (descMap_eq_algHom hN B g))

end Uniqueness

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


/-- The projection `j : E → D` of a subsystem is **strict**. -/
theorem Subsystem.proj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.proj := by
  intro X hrel
  rw [Subsystem.proj_rel] at hrel
  obtain ⟨_, hXD, hsub⟩ := hrel
  exact Set.Subset.antisymm (D.sub_master hXD) (by rw [h.master_eq]; exact hsub)

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


/-- `i ∘ j = I_Exp` at the raw level (from the iso's `inv_hom_id`). -/
theorem expHom_comp_expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expHom N hN).comp (expInv N hN) = idMap (Exp N hN).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).inv_hom_id
  exact h

end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


/-- **Every homomorphism `g : Exp → D` is a fixed point** of the operator `λh. k ∘ T(h) ∘ j`. This is
the homomorphism square `g ∘ i = k ∘ T(g)` (`g.comm`) rearranged by `i ∘ j = I`. -/
theorem algHom_fix (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1 = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1
      = (g.hom.1).comp (idMap (Exp N hN).sys) := (comp_idMap _).symm
    _ = (g.hom.1).comp ((expHom N hN).comp (expInv N hN)) := by rw [expHom_comp_expInv]
    _ = ((g.hom.1).comp (expHom N hN)).comp (expInv N hN) := (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp (expInv N hN) :=
          congrArg (fun m => m.comp (expInv N hN)) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := comp_assoc _ _ _

end Existence
end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


/-- **`descAlgHom` is the least homomorphism**: `val ≤ g` for every homomorphism `g : Exp → D`. The
Kleene iterates `valₙ` lie below any fixed point `g` (induction: `val₀ = ⊥ ≤ g`, and the operator is
monotone with `g` its own fixed point), so their union `val` does too. This is the easy half of
initiality; the matching `g ≤ val` (so `g = val`) is the projection-chain argument of Phase 4. -/
theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

end Existence
end Exercise619
end

section
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


theorem descMap_le_algHom (g : AlgHom (ExpAlg N hN) B) : descMap hN B ≤ g.hom.1 := by
  intro X Y hr
  obtain ⟨n, hn⟩ := hr
  exact descRel_le_algHom hN B g n X Y hn

end Existence
end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_623 : ∀ {N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys}
  (hN :
    @Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N))
  (g :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
      (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B),
  @LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
          DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
          (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)))
    (@DomainTheory.NeighbourhoodSystems.Exercise619.descMap N hN B)
    (@Subtype.val
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
            (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (fun
          (f :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
                  (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys) =>
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
              (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys
          f)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
        DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
        (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
        (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B g)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise619.descMap_le_algHom
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

section
namespace Exercise624

/-- The first right-hand side `D + (D × E)`. -/
def Fsol (D E : ScottSys) : ScottSys := D.sum (D.prod E)

end Exercise624
end

section
namespace Exercise624

/-- The second right-hand side `D + E`. -/
def Gsol (D E : ScottSys) : ScottSys := D.sum E

end Exercise624
end

section
namespace Exercise624

/-- `gTok p q = tok((D + E))` for `D = {p}`, `E = {q}`: the tagged union `{Λ} ∪ 0p ∪ 1q`. It is also
the master of the product `{p} × {q}` (sum and product share the master shape over `{0,1}*`). -/
def gTok (p q : Set Str) : Set Str := insert ([] : Str) (embBit false p ∪ embBit true q)

end Exercise624
end

section
namespace Exercise624

/-- `fTok p q = tok((D + (D×E)))` for `D = {p}`, `E = {q}`: `{Λ} ∪ 0p ∪ 1(gTok p q)`, equivalently
`gTok p (gTok p q)`. -/
def fTok (p q : Set Str) : Set Str := gTok p (gTok p q)

end Exercise624
end

section
namespace Exercise624

/-- The pair iteration `Φ(p, q) = (fTok p q, gTok p q)` from the bottom pair `({Λ}, {Λ})`. -/
def pIter : ℕ → Set Str × Set Str
  | 0 => ({([] : Str)}, {([] : Str)})
  | n + 1 => (fTok (pIter n).1 (pIter n).2, gTok (pIter n).1 (pIter n).2)

end Exercise624
end

section
namespace Exercise624

/-- The first component of the double fixed point, `Γ_D = ⋃ₙ (Φⁿ).₁`. -/
def GammaD : Set Str := ⋃ n, (pIter n).1

end Exercise624
end

section
namespace Exercise624

/-- The second component of the double fixed point, `Γ_E = ⋃ₙ (Φⁿ).₂`. -/
def GammaE : Set Str := ⋃ n, (pIter n).2

end Exercise624
end

section
namespace Exercise624

theorem nil_mem_GammaD : ([] : Str) ∈ GammaD := Set.mem_iUnion.mpr ⟨0, rfl⟩

end Exercise624
end

section
namespace Exercise624

/-- The solution system `D = {Γ_D}`. -/
def Dsol : ScottSys := singletonSys GammaD ⟨[], nil_mem_GammaD⟩

end Exercise624
end

section
namespace Exercise624

theorem nil_mem_GammaE : ([] : Str) ∈ GammaE := Set.mem_iUnion.mpr ⟨0, rfl⟩

end Exercise624
end

section
namespace Exercise624

/-- The solution system `E = {Γ_E}`. -/
def Esol : ScottSys := singletonSys GammaE ⟨[], nil_mem_GammaE⟩

end Exercise624
end

section
namespace Exercise624


/-- `gTok` is monotone in both arguments. -/
theorem gTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : gTok p q ⊆ gTok p' q' := by
  rintro w (rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩)
  · exact Set.mem_insert _ _
  · exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

end Exercise624
end

section
namespace Exercise624


/-- `fTok` is monotone in both arguments. -/
theorem fTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : fTok p q ⊆ fTok p' q' :=
  gTok_mono hp (gTok_mono hp hq)

end Exercise624
end

section
namespace Exercise624


/-- The master (token set) of `D + (D×E)` is `fTok Γ_D Γ_E` — definitionally, the sum/product
masters expand to the tagged-union shape `gTok`/`fTok`. -/
theorem master_Fsol : (Fsol Dsol Esol).sys.master = fTok GammaD GammaE := rfl

end Exercise624
end

section
namespace Exercise624


/-- The master (token set) of `D + E` is `gTok Γ_D Γ_E`. -/
theorem master_Gsol : (Gsol Dsol Esol).sys.master = gTok GammaD GammaE := rfl

end Exercise624
end

section
namespace Exercise624


theorem nil_mem_fTok (p q : Set Str) : ([] : Str) ∈ fTok p q := Set.mem_insert _ _

end Exercise624
end

section
namespace Exercise624


theorem nil_mem_gTok (p q : Set Str) : ([] : Str) ∈ gTok p q := Set.mem_insert _ _

end Exercise624
end

section
namespace Exercise624


/-- **Additivity of `fTok`.** Every token of `fTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`fTok aₙ bₙ`. The nested `true`-branch (the product copy `0p` inside `1(gTok p q)`) still references
at most one coordinate, so a single finite stage suffices. -/
theorem mem_fTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ fTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ fTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨u, rfl, hu⟩
  · exact ⟨0, nil_mem_fTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · rcases hu with rfl | ⟨u', rfl, hu'⟩ | ⟨u', rfl, hu'⟩
    · exact ⟨0, Or.inr (Or.inr ⟨[], rfl, nil_mem_gTok _ _⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨false :: u', rfl, Or.inr (Or.inl ⟨u', rfl, hn⟩)⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨true :: u', rfl, Or.inr (Or.inr ⟨u', rfl, hn⟩)⟩)⟩

end Exercise624
end

section
namespace Exercise624


/-- **Additivity of `gTok`.** Every token of `gTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`gTok aₙ bₙ` — each token references at most one coordinate. -/
theorem mem_gTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ gTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ gTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩
  · exact ⟨0, nil_mem_gTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inr ⟨w', rfl, hn⟩)⟩

end Exercise624
end

section
namespace Exercise624


/-- Each stage sits inside the colimit `Γ_D` (choice-free; avoids `Set.subset_iUnion`). -/
theorem pIter_fst_subset_GammaD (m : ℕ) : (pIter m).1 ⊆ GammaD :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

end Exercise624
end

section
namespace Exercise624


/-- Each stage sits inside the colimit `Γ_E` (choice-free). -/
theorem pIter_snd_subset_GammaE (m : ℕ) : (pIter m).2 ⊆ GammaE :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

end Exercise624
end

section
namespace Exercise624


/-- **First equation of the double fixed point:** `fTok Γ_D Γ_E = Γ_D`, i.e. `tok(D + (D×E)) = Γ_D`
for `D = {Γ_D}`, `E = {Γ_E}`. -/
theorem fTok_GammaD_GammaE : fTok GammaD GammaE = GammaD := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_fTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_fTok _ _
    | succ m =>
        exact fTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

end Exercise624
end

section
namespace Exercise624


/-- **`{Γ_D} ◁ D + (D × E)`.** The singleton system `D = {Γ_D}` is a subsystem of `D + (D×E)`: by the
fixed point its only neighbourhood `Γ_D` is the master of `D + (D×E)`. -/
theorem Dsol_subsystem : Dsol.sys ◁ (Fsol Dsol Esol).sys := by
  have hmaster : (Fsol Dsol Esol).sys.master = GammaD := master_Fsol.trans fTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaD := hX
    rw [hXeq, ← hmaster]
    exact (Fsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaD
    rw [show X = GammaD from hX, show Y = GammaD from hY, Set.inter_self]

end Exercise624
end

section
namespace Exercise624


/-- **Second equation of the double fixed point:** `gTok Γ_D Γ_E = Γ_E`, i.e. `tok(D + E) = Γ_E`. -/
theorem gTok_GammaD_GammaE : gTok GammaD GammaE = GammaE := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_gTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_gTok _ _
    | succ m =>
        exact gTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

end Exercise624
end

section
namespace Exercise624


/-- **`{Γ_E} ◁ D + E`.** The singleton system `E = {Γ_E}` is a subsystem of `D + E`: by the fixed
point its only neighbourhood `Γ_E` is the master of `D + E`. -/
theorem Esol_subsystem : Esol.sys ◁ (Gsol Dsol Esol).sys := by
  have hmaster : (Gsol Dsol Esol).sys.master = GammaE := master_Gsol.trans gTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaE := hX
    rw [hXeq, ← hmaster]
    exact (Gsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaE
    rw [show X = GammaE from hX, show Y = GammaE from hY, Set.inter_self]

end Exercise624
end

section
namespace Exercise624


/-- **The double fixed point (token level).** There is a pair of token sets `(Γ_D, Γ_E)`, both
containing `Λ`, that solve the two coupled token equations `tok(D + (D×E)) = Γ_D` and
`tok(D + E) = Γ_E` simultaneously. -/
theorem exists_double_fixedPoint :
    ∃ Γd Γe : Set Str, ([] : Str) ∈ Γd ∧ ([] : Str) ∈ Γe ∧
      fTok Γd Γe = Γd ∧ gTok Γd Γe = Γe :=
  ⟨GammaD, GammaE, nil_mem_GammaD, nil_mem_GammaE, fTok_GammaD_GammaE, gTok_GammaD_GammaE⟩

end Exercise624
end

section
namespace Exercise624


/- concordance: source L4161 EXERCISE 6.24 recursive domain equations -/
/-- **Exercise 6.24 (object level).** By the double fixed-point method there exist `∅`-free systems
`D`, `E` over `{0,1}*` such that `{D} ◁ D + (D×E)` and `{E} ◁ D + E` **simultaneously**. These two
facts are exactly the joint hypothesis of the simultaneous Theorem 6.14, which then yields the
required isomorphisms `D ≅ D + (D×E)` and `E ≅ D + E`. -/
theorem exists_simultaneous_subsystems :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Dsol, Esol, Dsol_subsystem, Esol_subsystem⟩

end Exercise624
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise624
section
set_option linter.unusedVariables false

theorem example_624 : ∃ (D : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys) (E :
  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str D.sys
      (D.sum (D.prod E)).sys)
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str E.sys (D.sum E).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise624.exists_simultaneous_subsystems
end

end DomainTheory.NeighbourhoodSystems.Exercise624
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-- The master neighbourhood `{Λ} ∪ 0Δ` of the lift. -/
def liftTokMaster (D : NeighborhoodSystem Str) : Set Str := insert [] (embBit false D.master)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem embF_subset_liftTokMaster {X : Set Str} (hX : D.mem X) :
    embBit false X ⊆ liftTokMaster D :=
  (embBit_subset.mpr (D.sub_master hX)).trans (Set.subset_insert _ _)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem liftTokMaster_inter_embF {X : Set Str} (hX : D.mem X) :
    liftTokMaster D ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_liftTokMaster hX)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem nil_mem_liftTokMaster : ([] : Str) ∈ liftTokMaster D := Set.mem_insert _ _

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem embF_ne_liftTokMaster {X : Set Str} : embBit false X ≠ liftTokMaster D := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_liftTokMaster)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

/- concordance: source L4187 EXERCISE 6.26 lifting a domain -/
/-- **Exercise 6.26 — the lifted system `𝒟_⊥` over `{0,1}*`.** A neighbourhood is the master
`{Λ} ∪ 0Δ` or a tagged copy `0X` (`X ∈ 𝒟`). `∅`-freeness of `𝒟` (`hD`) keeps it `∅`-free. -/
def liftTok (D : NeighborhoodSystem Str) (_hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = liftTokMaster D ∨ ∃ X, D.mem X ∧ W = embBit false X
  master := liftTokMaster D
  master_nonempty := ⟨[], nil_mem_liftTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_liftTokMaster hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [liftTokMaster_inter_embF hX']; exact Or.inr ⟨X', hX', rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_comm, liftTokMaster_inter_embF hX]; exact Or.inr ⟨X, hX, rfl⟩
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z', hZ', rfl⟩
        · exact absurd (hZsub nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X ∩ X', D.inter_mem hX hX' hZ' (embBit_subset.mp hZsub), rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **fresh bottom** of `𝒟_⊥`: the element whose only neighbourhood is the master `{Λ} ∪ 0Δ`. -/
def liftBot (D : NeighborhoodSystem Str) (hD : ∀ X, D.mem X → X.Nonempty) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D
  sub := by rintro W rfl; exact Or.inl rfl
  master_mem := rfl
  inter_mem := by rintro W W' rfl rfl; rw [Set.inter_self]
  up_mem := by
    rintro W W' rfl hW' hsub
    exact Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_embF {X : Set Str} (hX : D.mem X) :
    (liftTok D hD).mem (embBit false X) := Or.inr ⟨X, hX, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_embF_inv {W : Set Str} (h : (liftTok D hD).mem (embBit false W)) : D.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem liftTok_nonempty (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ W, (liftTok D hD).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩)
  · exact ⟨[], nil_mem_liftTokMaster⟩
  · exact embBit_nonempty (hD X hX)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-- The **lift object** `𝒟_⊥` of Scott's category. -/
def ScottSys.lift (A : ScottSys) : ScottSys := ⟨liftTok A.sys A.ne, liftTok_nonempty A.ne⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **embedding** `|𝒟| ↪ |𝒟_⊥|`: `liftUp x = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ x}`, the image of `x`
sitting above the fresh bottom. -/
def liftUp {D : NeighborhoodSystem Str} {hD : ∀ X, D.mem X → X.Nonempty} (x : D.Element) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, x.sub hX, rfl⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [liftTokMaster_inter_embF (x.sub hX')]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, liftTokMaster_inter_embF (x.sub hX)]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embBit_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', x.up_mem hX hX' (embBit_subset.mp hsub), rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

@[simp] theorem mem_liftBot {W : Set Str} : (liftBot D hD).mem W ↔ W = liftTokMaster D := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

@[simp] theorem mem_liftUp {x : D.Element} {W : Set Str} :
    (liftUp (hD := hD) x).mem W ↔ W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X := Iff.rfl

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

/-- **`f_⊥`, the action of lifting on (approximable) maps.** It carries the master to the master (so
it is strict) and a copy `0X` to `0X'` whenever `X f X'`. -/
def liftMapTok (f : ApproximableMap A.sys B.sys) :
    ApproximableMap (ScottSys.lift A).sys (ScottSys.lift B).sys where
  rel W W' :=
    ((liftTok A.sys A.ne).mem W ∧ W' = liftTokMaster B.sys) ∨
    (∃ X X', f.rel X X' ∧ W = embBit false X ∧ W' = embBit false X')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩)
    · exact hW
    · exact liftTok_mem_embF (hD := A.ne) (f.rel_dom hrel)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact liftTok_mem_embF (hD := B.ne) (f.rel_cod hrel)
  master_rel := Or.inl ⟨(ScottSys.lift A).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr ⟨X, X', hrel, hWeq, by rw [liftTokMaster_inter_embF (f.rel_cod hrel)]⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr ⟨X, X', hrel, rfl, ?_⟩
        rw [Set.inter_comm, liftTokMaster_inter_embF (f.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr ⟨X, X' ∩ X'₂, f.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((ScottSys.lift B).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZ'mem with rfl | ⟨X₃, hX₃, rfl⟩
      · exact Or.inl ⟨hZmem, rfl⟩
      · rcases hZmem with rfl | ⟨X₂, hX₂, rfl⟩
        · exact absurd (hWW nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X₂, X₃,
            f.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_embFF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit false (embBit false W))) : D.sys.mem W :=
  liftTok_mem_embF_inv (hD := D.ne)
    (oplusTok_mem_embF_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_embTF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit true (embBit false W))) : E.sys.mem W :=
  liftTok_mem_embF_inv (hD := E.ne)
    (oplusTok_mem_embT_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_mem_embFF {X' : Set Str} (hX' : D.sys.mem X') :
    (D.lift.oplus E.lift).sys.mem (embBit false (embBit false X')) :=
  oplusTok_mem_embF (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := D.ne) hX') (embF_ne_liftTokMaster (D := D.sys))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem o_mem_embTF {Y' : Set Str} (hY' : E.sys.mem Y') :
    (D.lift.oplus E.lift).sys.mem (embBit true (embBit false Y')) :=
  oplusTok_mem_embT (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := E.ne) hY') (embF_ne_liftTokMaster (D := E.sys))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The forward half `|𝒟_⊥ ⊕ ℰ_⊥| → |𝒟 + ℰ|`: delete the inner `0`. -/
def toSumLift (z : (D.lift.oplus E.lift).sys.Element) : (D.sum E).sys.Element where
  mem W := W = sumTokMaster D.sys E.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false X ∧ z.mem (embBit false (embBit false X)))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true Y ∧ z.mem (embBit true (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX
    · exact sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embBit_inter, embBit_inter] at hz
        exact o_embFF_inv (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embBit_inter, embBit_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embBit_inter, embBit_inter] at hz
        exact o_embTF_inv (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embBit_inter, embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.sum E).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X'', hX'', rfl, ?_⟩)
        exact z.up_mem hzX (o_mem_embFF hX'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide) (D.ne X hX) hs)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide) (E.ne Y hY) hs)
      · refine Or.inr (Or.inr ⟨Y'', hY'', rfl, ?_⟩)
        exact z.up_mem hzY (o_mem_embTF hY'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem toSumLift_mem_embF {z : (D.lift.oplus E.lift).sys.Element} {X : Set Str}
    (hX : D.sys.mem X) :
    (toSumLift z).mem (embBit false X) ↔ z.mem (embBit false (embBit false X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (D.ne X hX))
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem toSumLift_mem_embT {z : (D.lift.oplus E.lift).sys.Element} {Y : Set Str}
    (hY : E.sys.mem Y) :
    (toSumLift z).mem (embBit true Y) ↔ z.mem (embBit true (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide) (E.ne Y hY))
    · rwa [embBit_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The inverse half `|𝒟 + ℰ| → |𝒟_⊥ ⊕ ℰ_⊥|`: reinstate the inner `0`. -/
def fromSumLift (s : (D.sum E).sys.Element) : (D.lift.oplus E.lift).sys.Element where
  mem W := W = sumTokMaster D.lift.sys E.lift.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false (embBit false X) ∧ s.mem (embBit false X))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true (embBit false Y) ∧ s.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact o_mem_embFF hX
    · exact o_mem_embTF hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr (Or.inl ⟨X', hX', ?_, hsX'⟩)
      rw [sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX')]
    · refine Or.inr (Or.inr ⟨Y', hY', ?_, hsY'⟩)
      rw [sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY')]
    · refine Or.inr (Or.inl ⟨X, hX, ?_, hsX⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX)]
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [embBit_inter] at hs
        exact sumTok_mem_embF_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [embBit_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y, hY, ?_, hsY⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY)]
    · exfalso
      have hs := s.inter_mem hsY hsX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [embBit_inter] at hs
        exact sumTok_mem_embT_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [embBit_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.oplus E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hV with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inl ⟨X'', hX''D, rfl, ?_⟩)
          exact s.up_mem hsX (sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX''D)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide)
            (embBit_nonempty (D.ne X hX)) hs)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide)
            (embBit_nonempty (E.ne Y hY)) hs)
      · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inr ⟨Y'', hY''E, rfl, ?_⟩)
          exact s.up_mem hsY (sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY''E)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem fromSumLift_mem_embFF {s : (D.sum E).sys.Element} {X : Set Str} (hX : D.sys.mem X) :
    (fromSumLift s).mem (embBit false (embBit false X)) ↔ s.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective (embBit_injective heq)]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide)
        (embBit_nonempty (D.ne X hX)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem fromSumLift_mem_embTF {s : (D.sum E).sys.Element} {Y : Set Str} (hY : E.sys.mem Y) :
    (fromSumLift s).mem (embBit true (embBit false Y)) ↔ s.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide)
        (embBit_nonempty (E.ne Y hY)))
    · rwa [embBit_injective (embBit_injective heq)]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem fromSumLift_toSumLift (z : (D.lift.oplus E.lift).sys.Element) :
    fromSumLift (toSumLift z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toSumLift_mem_embF hX).mp hs
    · exact (toSumLift_mem_embT hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X', hX'D, rfl⟩
      · exact absurd rfl hXne
      · exact Or.inr (Or.inl ⟨X', hX'D, rfl, (toSumLift_mem_embF hX'D).mpr hW⟩)
    · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
      · exact absurd rfl hYne
      · exact Or.inr (Or.inr ⟨Y', hY'E, rfl, (toSumLift_mem_embT hY'E).mpr hW⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem lp_mem_embF {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y')) :=
  liftTok_mem_embF (hD := (D.prod E).ne) (prodTok_mem_prodTokNbhd hX' hY')

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem lp_prod_inv {X' Y' : Set Str}
    (h : (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨A, B, hA, hB, heq⟩ := liftTok_mem_embF_inv (hD := (D.prod E).ne) h
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
  exact ⟨hA, hB⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem ot_mem_prod {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y')) :=
  otimesTok_mem_prod (liftTok_mem_embF (hD := D.ne) hX') (liftTok_mem_embF (hD := E.ne) hY')
    (embF_ne_liftTokMaster (D := D.sys)) (embF_ne_liftTokMaster (D := E.sys))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem ot_mem_prod_inv {X' Y' : Set Str}
    (h : (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨h1, h2⟩ := otimesTok_mem_prod_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys) h
    (embF_ne_liftTokMaster (D := D.sys))
  exact ⟨liftTok_mem_embF_inv (hD := D.ne) h1, liftTok_mem_embF_inv (hD := E.ne) h2⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The forward half `|𝒟_⊥ ⊗ ℰ_⊥| → |(𝒟 × ℰ)_⊥|`. -/
def toLiftProd (z : (D.lift.otimes E.lift).sys.Element) : (D.prod E).lift.sys.Element where
  mem W := W = liftTokMaster (prodTok D.sys E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = embBit false (prodTokNbhd X Y) ∧
        z.mem (prodTokNbhd (embBit false X) (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact lp_mem_embF hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hzXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hzXY'⟩
      rw [liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX' hY')]
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hzXY⟩
      rw [Set.inter_comm, liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX hY)]
    · have hz := z.inter_mem hzXY hzXY'
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter] at hz
      obtain ⟨hXi, hYi⟩ := ot_mem_prod_inv (z.sub hz)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hz⟩
      rw [embBit_inter, prodTokNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.prod E).lift.sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨Z, hZ, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X'', Y'', hX'', hY'', rfl⟩ := hZ
        refine Or.inr ⟨X'', Y'', hX'', hY'', rfl, ?_⟩
        obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp (embBit_subset.mp hsub)
        exact z.up_mem hzXY (ot_mem_prod hX'' hY'')
          (prodTokNbhd_subset_iff.mpr ⟨embBit_subset.mpr hsX, embBit_subset.mpr hsY⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem toLiftProd_mem_embF {z : (D.lift.otimes E.lift).sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (toLiftProd z).mem (embBit false (prodTokNbhd X Y)) ↔
      z.mem (prodTokNbhd (embBit false X) (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hz⟩)
    · exact absurd h0 (embF_ne_liftTokMaster (D := prodTok D.sys E.sys))
    · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective (embBit_injective heq); exact hz
  · intro hz; exact Or.inr ⟨X, Y, hX, hY, rfl, hz⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The inverse half `|(𝒟 × ℰ)_⊥| → |𝒟_⊥ ⊗ ℰ_⊥|`. -/
def fromLiftProd (s : (D.prod E).lift.sys.Element) : (D.lift.otimes E.lift).sys.Element where
  mem W := W = prodTokNbhd (liftTokMaster D.sys) (liftTokMaster E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = prodTokNbhd (embBit false X) (embBit false Y) ∧
        s.mem (embBit false (prodTokNbhd X Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact ot_mem_prod hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hsXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hsXY'⟩
      rw [prodTokNbhd_inter, liftTokMaster_inter_embF hX', liftTokMaster_inter_embF hY']
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hsXY⟩
      rw [Set.inter_comm, prodTokNbhd_inter, liftTokMaster_inter_embF hX,
        liftTokMaster_inter_embF hY]
    · have hs := s.inter_mem hsXY hsXY'
      rw [embBit_inter, prodTokNbhd_inter] at hs
      obtain ⟨hXi, hYi⟩ := lp_prod_inv (s.sub hs)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hs⟩
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.otimes E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨U, V, hU, hV, hUne, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hU with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hUne
        · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hVne
          · refine Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, ?_⟩
            obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
            exact s.up_mem hsXY (lp_mem_embF hX''D hY''E)
              (embBit_subset.mpr (prodTokNbhd_subset_iff.mpr
                ⟨embBit_subset.mp hsX, embBit_subset.mp hsY⟩))

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem fromLiftProd_mem_prod {s : (D.prod E).lift.sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (fromLiftProd s).mem (prodTokNbhd (embBit false X) (embBit false Y)) ↔
      s.mem (embBit false (prodTokNbhd X Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hs⟩)
    · obtain ⟨hX0, -⟩ := prodTokNbhd_injective h0
      exact absurd hX0 (embF_ne_liftTokMaster (D := D.sys))
    · obtain ⟨hXe, hYe⟩ := prodTokNbhd_injective heq
      rw [embBit_injective hXe, embBit_injective hYe]; exact hs
  · intro hs; exact Or.inr ⟨X, Y, hX, hY, rfl, hs⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem fromLiftProd_toLiftProd (z : (D.lift.otimes E.lift).sys.Element) :
    fromLiftProd (toLiftProd z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toLiftProd_mem_embF hX hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
      · exact absurd rfl hXne
      · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hYne
        · exact Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, (toLiftProd_mem_embF hX''D hY''E).mpr hW⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem toLiftProd_fromLiftProd (s : (D.prod E).lift.sys.Element) :
    toLiftProd (fromLiftProd s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromLiftProd_mem_prod hX hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨Z, hZ, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, Y, hX, hY, rfl⟩ := hZ
      exact Or.inr ⟨X, Y, hX, hY, rfl, (fromLiftProd_mem_prod hX hY).mpr hW⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The order-isomorphism `|𝒟_⊥ ⊗ ℰ_⊥| ≃o |(𝒟 × ℰ)_⊥|`. -/
def liftProdEquiv : (D.lift.otimes E.lift).sys.Element ≃o (D.prod E).lift.sys.Element where
  toFun := toLiftProd
  invFun := fromLiftProd
  left_inv := fromLiftProd_toLiftProd
  right_inv := toLiftProd_fromLiftProd
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hXne
        · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hYne
          · exact (toLiftProd_mem_embF hX''D hY''E).mp
              (h _ ((toLiftProd_mem_embF hX''D hY''E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, Y, hX, hY, rfl, h _ hzXY⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

theorem toSumLift_fromSumLift (s : (D.sum E).sys.Element) :
    toSumLift (fromSumLift s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromSumLift_mem_embFF hX).mp hs
    · exact (fromSumLift_mem_embTF hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromSumLift_mem_embFF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromSumLift_mem_embTF hY).mpr hW⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

/-- The order-isomorphism `|𝒟_⊥ ⊕ ℰ_⊥| ≃o |𝒟 + ℰ|`. -/
def sumLiftEquiv : (D.lift.oplus E.lift).sys.Element ≃o (D.sum E).sys.Element where
  toFun := toSumLift
  invFun := fromSumLift
  left_inv := fromSumLift_toSumLift
  right_inv := toSumLift_fromSumLift
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X', hX'D, rfl⟩
        · exact absurd rfl hXne
        · exact (toSumLift_mem_embF hX'D).mp (h _ ((toSumLift_mem_embF hX'D).mpr hW))
      · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
        · exact absurd rfl hYne
        · exact (toSumLift_mem_embT hY'E).mp (h _ ((toSumLift_mem_embT hY'E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **unlift** of an element that lies above the fresh bottom (i.e. contains `0Δ`): the
`𝒟`-element `{X ∣ 0X ∈ z}`. -/
def unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) : D.Element where
  mem X := z.mem (embBit false X)
  sub := fun hX => liftTok_mem_embF_inv (z.sub hX)
  master_mem := hz
  inter_mem := by
    intro X X' hX hX'
    have hz' := z.inter_mem hX hX'
    rwa [embBit_inter] at hz'
  up_mem := by
    intro X Y hX hY hXY
    exact z.up_mem hX (liftTok_mem_embF hY) (embBit_subset.mpr hXY)

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


/-- `liftBot` is the least element of `𝒟_⊥`. -/
theorem liftBot_le (z : (liftTok D hD).Element) : liftBot D hD ≤ z := by
  rintro W rfl; exact z.master_mem

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


/-- The fresh bottom is *strictly* below every lifted element. -/
theorem liftBot_lt_liftUp (x : D.Element) : liftBot D hD < liftUp (hD := hD) x := by
  refine lt_of_le_of_ne (liftBot_le _) (fun heq => ?_)
  have hmem : (liftBot D hD).mem (embBit false D.master) := by
    rw [heq]; exact Or.inr ⟨D.master, x.master_mem, rfl⟩
  exact embF_ne_liftTokMaster hmem

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


/-- **`(g ∘ f)_⊥ = g_⊥ ∘ f_⊥`.** -/
theorem liftMapTok_comp (f : ApproximableMap A.sys B.sys) (g : ApproximableMap B.sys C.sys) :
    liftMapTok (g.comp f) = (liftMapTok g).comp (liftMapTok f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨liftTokMaster B.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(ScottSys.lift B).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr ⟨X, X', hf, rfl, rfl⟩, Or.inr ⟨X', X'', hg, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩
      · exact Or.inl ⟨liftTok_mem_embF (hD := A.ne) (f.rel_dom hf), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


/-- **`(I_𝒟)_⊥ = I_{𝒟_⊥}`.** -/
theorem liftMapTok_id : liftMapTok (idMap A.sys) = idMap (ScottSys.lift A).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (ScottSys.lift A).sys.master_mem, (ScottSys.lift A).sys.sub_master hW⟩
    · exact ⟨liftTok_mem_embF (hD := A.ne) hX, liftTok_mem_embF (hD := A.ne) hX',
        embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩
      · exact absurd (hsub nil_mem_liftTokMaster) nil_not_mem_embBit
      · exact Or.inr ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


/-- **`f_⊥` is strict** for *any* `f`: the master `Λ`-bearing input relates only to the master. -/
theorem liftMapTok_isStrict (f : ApproximableMap A.sys B.sys) : IsStrict (liftMapTok f) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩)
  · rfl
  · have hnil : ([] : Str) ∈ embBit false X := by
      rw [← heq]; exact nil_mem_liftTokMaster
    exact absurd hnil nil_not_mem_embBit

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_master : (liftTok D hD).mem (liftTokMaster D) := Or.inl rfl

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


/-- `liftUp` is an order embedding: `liftUp x ⊑ liftUp y ↔ x ⊑ y`. -/
theorem liftUp_le_liftUp_iff {x y : D.Element} :
    liftUp (hD := hD) x ≤ liftUp (hD := hD) y ↔ x ≤ y := by
  constructor
  · intro h X hX
    have hmem := h (embBit false X) (Or.inr ⟨X, hX, rfl⟩)
    rcases hmem with h0 | ⟨X', hX', heq⟩
    · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rw [embBit_injective heq]; exact hX'
  · rintro h W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h X hX, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


theorem liftUp_unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) :
    liftUp (hD := hD) (unlift z hz) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl⟩)
    · exact z.master_mem
    · exact hX
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, hW, rfl⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


/-- **Exercise 6.26 — "describe in terms of elements".** Every element of `𝒟_⊥` is either the fresh
bottom or a lifted `𝒟`-element: `|𝒟_⊥| ≅ |𝒟|_⊥`. (`Prop`-level; the case split on "does `z` contain
`0Δ`?" uses excluded middle — the only non-constructive step in this module.) -/
theorem eq_liftBot_or_exists_liftUp (z : (liftTok D hD).Element) :
    z = liftBot D hD ∨ ∃ x : D.Element, z = liftUp (hD := hD) x := by
  by_cases hz : z.mem (embBit false D.master)
  · exact Or.inr ⟨unlift z hz, (liftUp_unlift z hz).symm⟩
  · refine Or.inl ?_
    apply NeighborhoodSystem.Element.ext
    intro W
    constructor
    · intro hW
      rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
      · rfl
      · exact absurd
          (z.up_mem hW (liftTok_mem_embF D.master_mem) (embBit_subset.mpr (D.sub_master hX))) hz
    · rintro rfl; exact z.master_mem

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


variable {D E : ScottSys}


/-- **Exercise 6.26 — `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`.** Coalescing the fresh bottoms of the two lifts
reproduces the separated sum. -/
theorem lift_oplus_lift_iso_sum :
    (D.lift.oplus E.lift).sys ≅ᴰ (D.sum E).sys := ⟨sumLiftEquiv⟩

end Exercise619
end

section
namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


variable {D E : ScottSys}


/-- **Exercise 6.26 — `𝒟_⊥ ⊗ ℰ_⊥ ≅ (𝒟 × ℰ)_⊥`** (the answer to Scott's `??`). The smash product of
two lifts is the lift of the product. -/
theorem lift_otimes_lift_iso_lift_prod :
    (D.lift.otimes E.lift).sys ≅ᴰ (D.prod E).lift.sys := ⟨liftProdEquiv⟩

end Exercise619
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise619
section
set_option linter.unusedVariables false

theorem example_626 : And
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys) :=
  @And.intro
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys)
  (@And.intro
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys)
    @DomainTheory.NeighbourhoodSystems.Exercise619.eq_liftBot_or_exists_liftUp
    @DomainTheory.NeighbourhoodSystems.Exercise619.lift_oplus_lift_iso_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise619.lift_otimes_lift_iso_lift_prod
end

end DomainTheory.NeighbourhoodSystems.Exercise619
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The injection `i : 𝒟 → 𝒟 × ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟×ℰ ∧ (X,Δ₁) ⊆ W`. -/
def fstInj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap D₀ (prodTok D₀ D₁) where
  rel X W := D₀.mem X ∧ (prodTok D₀ D₁).mem W ∧ prodTokNbhd X D₁.master ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (prodTok D₀ D₁).master_mem, subset_rfl⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (prodTok D₀ D₁).inter_mem hW hW' (prodTok_mem_prodTokNbhd hX D₁.master_mem)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((prodTokNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩).trans hsub).trans hWW'⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The projection `j : 𝒟 × ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟×ℰ ∧ X ∈ 𝒟 ∧ W ⊆ (X,Δ₁)`. -/
def fstProj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap (prodTok D₀ D₁) D₀ where
  rel W X := (prodTok D₀ D₁).mem W ∧ D₀.mem X ∧ W ⊆ prodTokNbhd X D₁.master
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prodTok D₀ D₁).master_mem, D₀.master_mem, subset_rfl⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    obtain ⟨A, B, hA, hB, rfl⟩ := hW
    have hAX : A ⊆ X := (prodTokNbhd_subset_iff.mp hsub).1
    have hAX' : A ⊆ X' := (prodTokNbhd_subset_iff.mp hsub').1
    exact ⟨prodTok_mem_prodTokNbhd hA hB, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
      prodTokNbhd_subset_iff.mpr ⟨Set.subset_inter hAX hAX', D₁.sub_master hB⟩⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩))⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Element-level inclusion `|𝒟 →⊥ ℰ| → |𝒟 → ℰ|`. -/
def incl (φ : (strictFun V₀ V₁).Element) : (funSpace V₀ V₁).Element :=
  toFilter (toStrictMap φ).1

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem incl_mono : Monotone (incl (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab M hM
  obtain ⟨hMmem, haM⟩ := hM
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : (toStrictMap a).1 ≤ (toStrictMap b).1 := (strictFunEquiv V₀ V₁).monotone hab
  exact hle p.1 p.2 (haM p hp)

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The inclusion `i : 𝒟 →⊥ ℰ ↪ 𝒟 → ℰ`. -/
def inclMap : ApproximableMap (strictFun V₀ V₁) (funSpace V₀ V₁) :=
  ofMono (fun _ hW => incl ((strictFun V₀ V₁).principal hW))
    (fun _ _ hW hW' hW'W => incl_mono (((strictFun V₀ V₁).principal_le_iff hW hW').mpr hW'W))

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The left-copy generator: `0X` for proper `X`, the shared bottom `sumTokMaster` for `X = Δ₀`. The
set-builder `{w ∣ w ∈ sumTokMaster ∧ X = Δ₀}` keeps the *definition* choice-free. -/
def leftN (D₀ D₁ : NeighborhoodSystem Str) (X : Set Str) : Set Str :=
  embBit false X ∪ {w | w ∈ sumTokMaster D₀ D₁ ∧ X = D₀.master}

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem X_eq_master_of_embT_subset_leftN {B X : Set Str} (hB : B.Nonempty)
    (h : embBit true B ⊆ leftN D₀ D₁ X) : X = D₀.master := by
  obtain ⟨σ, hσ⟩ := hB
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', -⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; exact absurd hw'.1 (by decide)
  · exact hXm

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem X_eq_master_of_nil_mem_leftN {X : Set Str} (h : ([] : Str) ∈ leftN D₀ D₁ X) :
    X = D₀.master := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h nil_not_mem_embBit
  · exact h

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem embF_subset_leftN {X : Set Str} : embBit false X ⊆ leftN D₀ D₁ X :=
  Set.subset_union_left

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem leftN_master : leftN D₀ D₁ D₀.master = sumTokMaster D₀ D₁ := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨hw, -⟩)
    · exact embF_subset_sumTokMaster D₀.master_mem hw
    · exact hw
  · exact fun w hw => Or.inr ⟨hw, rfl⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem leftN_proper {X : Set Str} (hne : X ≠ D₀.master) : leftN D₀ D₁ X = embBit false X := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨-, hXm⟩)
    · exact hw
    · exact absurd hXm hne
  · exact embF_subset_leftN

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **only** classical step in Exercise 6.27: `leftN X` is an `𝒟 ⊕ ℰ`-neighbourhood. The proof
splits on the (undecidable for arbitrary `X`) test `X = Δ₀`. -/
theorem oplus_mem_leftN {X : Set Str} (hX : D₀.mem X) :
    (oplusTok D₀ D₁ h₀ h₁).mem (leftN D₀ D₁ X) := by
  by_cases h : X = D₀.master
  · rw [h, leftN_master]; exact (oplusTok D₀ D₁ h₀ h₁).master_mem
  · rw [leftN_proper h]; exact oplusTok_mem_embF hX h

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Strictification of a map** (on relations): keep `f` but force the master input to the master
output. The resulting map is strict, lies below `f`, and is the identity on strict maps. -/
def strictifyMap (g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Y := g.rel X Y ∧ (X = V₀.master → Y = V₁.master)
  rel_dom h := g.rel_dom h.1
  rel_cod h := g.rel_cod h.1
  master_rel := ⟨g.master_rel, fun _ => rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hg, hs⟩ ⟨hg', hs'⟩
    exact ⟨g.inter_right hg hg', fun hX => by rw [hs hX, hs' hX, Set.inter_self]⟩
  mono := by
    rintro X X' Y Y' ⟨hg, hs⟩ hX'X hYY' hX' hY'
    refine ⟨g.mono hg hX'X hYY' hX' hY', fun hX'm => ?_⟩
    have hX : V₀.mem X := g.rel_dom hg
    have hXm : X = V₀.master := Set.Subset.antisymm (V₀.sub_master hX) (hX'm ▸ hX'X)
    exact Set.Subset.antisymm (V₁.sub_master hY') ((hs hXm) ▸ hYY')

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strictifyMap_isStrict (g : ApproximableMap V₀ V₁) : IsStrict (strictifyMap g) :=
  fun _ h => h.2 rfl

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strictification as an element of the *strict* function space's token type. -/
def strictify (g : ApproximableMap V₀ V₁) : StrictMap V₀ V₁ := ⟨strictifyMap g, strictifyMap_isStrict g⟩

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Element-level strictification `|𝒟 → ℰ| → |𝒟 →⊥ ℰ|`. -/
def strct (ψ : (funSpace V₀ V₁).Element) : (strictFun V₀ V₁).Element :=
  toStrictFilter (strictify (toApproxMap ψ))

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strct_mono : Monotone (strct (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab W hW
  obtain ⟨hWmem, haW⟩ := hW
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : toApproxMap a ≤ toApproxMap b := (funSpaceEquiv V₀ V₁).monotone hab
  exact ⟨hle p.1 p.2 (haW p hp).1, (haW p hp).2⟩

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strictification retraction `j : 𝒟 → ℰ → 𝒟 →⊥ ℰ`. -/
def strctMap : ApproximableMap (funSpace V₀ V₁) (strictFun V₀ V₁) :=
  ofMono (fun _ hM => strct ((funSpace V₀ V₁).principal hM))
    (fun _ _ hM hM' hM'M => strct_mono (((funSpace V₀ V₁).principal_le_iff hM hM').mpr hM'M))

end Part5

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem subset_of_embF_subset_leftN {A X : Set Str} (hA : A ⊆ D₀.master)
    (h : embBit false A ⊆ leftN D₀ D₁ X) : A ⊆ X := by
  intro σ hσ
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', hw'X⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; rw [hw'.2]; exact hw'X
  · rw [hXm]; exact hA hσ

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem leftN_subset_iff {X X' : Set Str} (hX : D₀.mem X) (hX' : D₀.mem X') :
    leftN D₀ D₁ X ⊆ leftN D₀ D₁ X' ↔ X ⊆ X' := by
  constructor
  · intro h
    exact subset_of_embF_subset_leftN (D₀.sub_master hX) (embF_subset_leftN.trans h)
  · intro hXX'
    rintro w (⟨w', rfl, hw'⟩ | ⟨hw, hXm⟩)
    · exact embF_subset_leftN ⟨w', rfl, hXX' hw'⟩
    · exact Or.inr ⟨hw, Set.Subset.antisymm (D₀.sub_master hX') (hXm ▸ hXX')⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The injection `i : 𝒟 → 𝒟 ⊕ ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟⊕ℰ ∧ leftN X ⊆ W`. -/
def inlInj : ApproximableMap D₀ (oplusTok D₀ D₁ h₀ h₁) where
  rel X W := D₀.mem X ∧ (oplusTok D₀ D₁ h₀ h₁).mem W ∧ leftN D₀ D₁ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (oplusTok D₀ D₁ h₀ h₁).master_mem, leftN_master.le⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (oplusTok D₀ D₁ h₀ h₁).inter_mem hW hW' (oplus_mem_leftN hX)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((leftN_subset_iff hX' hX).mpr hX'X).trans (hsub.trans hWW')⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The projection `j : 𝒟 ⊕ ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟⊕ℰ ∧ X ∈ 𝒟 ∧ W ⊆ leftN X`. -/
def inlProj : ApproximableMap (oplusTok D₀ D₁ h₀ h₁) D₀ where
  rel W X := (oplusTok D₀ D₁ h₀ h₁).mem W ∧ D₀.mem X ∧ W ⊆ leftN D₀ D₁ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(oplusTok D₀ D₁ h₀ h₁).master_mem, D₀.master_mem, leftN_master.ge⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    rcases hW with rfl | ⟨A, hA, hAne, rfl⟩ | ⟨B, hB, hBne, rfl⟩
    · have hXm := X_eq_master_of_nil_mem_leftN (hsub nil_mem_sumTokMaster)
      have hX'm := X_eq_master_of_nil_mem_leftN (hsub' nil_mem_sumTokMaster)
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨Or.inl rfl, D₀.master_mem, leftN_master.ge⟩
    · have hAX : A ⊆ X := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub
      have hAX' : A ⊆ X' := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub'
      exact ⟨oplusTok_mem_embF hA hAne, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
        (embBit_subset.mpr (Set.subset_inter hAX hAX')).trans embF_subset_leftN⟩
    · have hXm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub
      have hX'm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub'
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨oplusTok_mem_embT hB hBne, D₀.master_mem, by
        rw [leftN_master]; exact embT_subset_sumTokMaster hB⟩
  mono := by
    rintro W W' X X' ⟨_, hX, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans ((leftN_subset_iff hX hX').mpr hXX'))⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- A concrete two-point domain over `{0,1}*`: neighbourhoods `Set.univ` (`= ⊥`) and `{[]}`. -/
def twoPt : NeighborhoodSystem Str where
  mem X := X = Set.univ ∨ X = {[]}
  master := Set.univ
  master_nonempty := ⟨[], Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro X (rfl | rfl)
    · exact subset_rfl
    · exact Set.subset_univ _
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [Set.univ_inter]; exact Or.inr rfl
    · rw [Set.inter_univ]; exact Or.inr rfl
    · rw [Set.inter_self]; exact Or.inr rfl

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The one-point unit domain `𝟙` over `{0,1}*` (only neighbourhood `{[]}`). -/
def unitPt : NeighborhoodSystem Str := (singletonSys ({[]} : Set Str) ⟨[], rfl⟩).sys

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/- concordance: source L4199 EXERCISE 6.27 which embeddings hold -/
/-- **Exercise 6.27 (4).** `𝒟 ⊴ 𝒟 ⊕ ℰ`. (Uses `Classical.choice` via `oplus_mem_leftN`.) -/
theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- Choice-free extensionality from agreement on principal inputs. Unlike `ext_of_toElementMap`
(which splits on the undecidable `V₀.mem X`), both sides of the relation carry domain membership via
`rel_dom`, so no case analysis — and hence no `Classical.choice` — is needed. -/
theorem ext_of_principal {γ δ : Type*} {W₀ : NeighborhoodSystem γ} {W₁ : NeighborhoodSystem δ}
    {f g : ApproximableMap W₀ W₁}
    (h : ∀ (X : Set γ) (hX : W₀.mem X),
      f.toElementMap (W₀.principal hX) = g.toElementMap (W₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


theorem fstInj_comp_fstProj_le (D₀ D₁ : NeighborhoodSystem Str) :
    (fstInj D₀ D₁).comp (fstProj D₀ D₁) ≤ idMap (prodTok D₀ D₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


theorem fstProj_comp_fstInj (D₀ D₁ : NeighborhoodSystem Str) :
    (fstProj D₀ D₁).comp (fstInj D₀ D₁) = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (prodTokNbhd_subset_iff.mp (hsub.trans hsub')).1⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨prodTokNbhd Z D₁.master,
      ⟨hX, prodTok_mem_prodTokNbhd hZ D₁.master_mem,
        prodTokNbhd_subset_iff.mpr ⟨hXZ, subset_rfl⟩⟩,
      prodTok_mem_prodTokNbhd hZ D₁.master_mem, hZ, subset_rfl⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


/-- **Exercise 6.27 (2).** `𝒟 ⊴ 𝒟 × ℰ`. -/
theorem fst_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    D₀ ⊴ prodTok D₀ D₁ :=
  trianglelefteq_of_projectionPair (fstInj D₀ D₁) (fstProj D₀ D₁)
    (fstProj_comp_fstInj D₀ D₁) (fstInj_comp_fstProj_le D₀ D₁)

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_subsystem_sumTok (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ◁ sumTok D₀ D₁ h₀ h₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF hX
    · exact sumTok_mem_embT hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact oplusTok_mem_embF hX' hX'ne
    · rw [sumTokMaster_inter_embT hY']; exact oplusTok_mem_embT hY' hY'ne
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact oplusTok_mem_embF hX hXne
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embF (sumTok_mem_embF_inv hInt)
        (inter_ne_of_ne_left (D₀.sub_master hX) hXne)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact oplusTok_mem_embT hY hYne
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embT (sumTok_mem_embT_inv hInt)
        (inter_ne_of_ne_left (D₁.sub_master hY) hYne)

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- **Exercise 6.27 (3).** `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`. -/
theorem oplus_trianglelefteq_sum (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ⊴ sumTok D₀ D₁ h₀ h₁ :=
  (oplusTok_subsystem_sumTok h₀ h₁).trianglelefteq

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


theorem otimesTok_subsystem_prodTok (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ◁ prodTok D₀ D₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
    · exact ⟨X, Y, hX, hY, rfl⟩
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
        Set.inter_eq_right.mpr (D₁.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
        Set.inter_eq_right.mpr (D₁.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      obtain ⟨A, B, hA, hB, heq⟩ := hInt
      obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
      exact Or.inr ⟨X ∩ X', Y ∩ Y', hA, hB,
        inter_ne_of_ne_left (D₀.sub_master hX) hXne,
        inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


/-- **Exercise 6.27 (1).** `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`. -/
theorem otimes_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ⊴ prodTok D₀ D₁ :=
  (otimesTok_subsystem_prodTok D₀ D₁).trianglelefteq

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- With the unit second factor, the smash `twoPt ⊗ 𝟙` collapses to its master. -/
theorem otimes_unitPt_collapse :
    ∀ W, (otimesTok twoPt unitPt).mem W → W = (otimesTok twoPt unitPt).master := by
  rintro W (rfl | ⟨X, Y, _, hY, _, hYne, rfl⟩)
  · rfl
  · exact absurd hY hYne

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem strictifyMap_le (g : ApproximableMap V₀ V₁) : strictifyMap g ≤ g := fun _ _ h => h.1

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem strictifyMap_of_isStrict {f : ApproximableMap V₀ V₁} (hf : IsStrict f) :
    strictifyMap f = f := by
  apply ApproximableMap.ext
  intro X Y
  exact ⟨fun h => h.1, fun h => ⟨h, fun hXm => hf (hXm ▸ h)⟩⟩

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- If a system's only neighbourhood is its master, its element lattice is a single point (`⊥`). -/
theorem subsingleton_element_of_only_master {γ : Type*} {V : NeighborhoodSystem γ}
    (h : ∀ X, V.mem X → X = V.master) : Subsingleton V.Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro X
  constructor
  · intro hx; have hXm := h X (x.sub hx); rw [hXm]; exact y.master_mem
  · intro hy; have hXm := h X (y.sub hy); rw [hXm]; exact x.master_mem

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


/-- **Exercise 6.27 (6).** `𝒟 ⊴ 𝒟 ⊗ ℰ` does **not** hold for all `𝒟, ℰ`: take `𝒟` two-point and
`ℰ = 𝟙`. Then `𝒟 ⊗ 𝟙` has a one-point element lattice while `𝒟` has two, so no isomorphism onto a
subsystem can exist. -/
theorem not_trianglelefteq_otimes :
    ¬ (twoPt ⊴ otimesTok twoPt unitPt) := by
  rintro ⟨D', hsub, ⟨e⟩⟩
  have hD'only : ∀ X, D'.mem X → X = D'.master := by
    intro X hX
    rw [otimes_unitPt_collapse X (hsub.sub hX)]; exact hsub.master_eq.symm
  have hss : Subsingleton D'.Element := subsingleton_element_of_only_master hD'only
  have hPmem : twoPt.mem ({[]} : Set Str) := Or.inr rfl
  have hne : twoPt.principal hPmem ≠ twoPt.principal twoPt.master_mem := by
    intro heq
    have h1 : (twoPt.principal hPmem).mem ({[]} : Set Str) := ⟨hPmem, subset_rfl⟩
    rw [heq] at h1
    obtain ⟨-, h2⟩ := h1
    exact absurd (Set.mem_singleton_iff.mp (h2 (Set.mem_univ ([false] : Str))) :
      ([false] : Str) = []) (by decide)
  exact hne (e.injective (hss.allEq (e (twoPt.principal hPmem))
    (e (twoPt.principal twoPt.master_mem))))

end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The four inverse identities of the two representation equivalences (defeq unfoldings). -/
theorem toApproxMap_toFilter (g : ApproximableMap V₀ V₁) : toApproxMap (toFilter g) = g :=
  (funSpaceEquiv V₀ V₁).apply_symm_apply g

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toElementMap_inclMap (φ : (strictFun V₀ V₁).Element) :
    inclMap.toElementMap φ = incl φ := by
  apply Element.ext
  intro M
  constructor
  · rintro ⟨W, hφW, _, hincl⟩
    obtain ⟨hMmem, hg⟩ := hincl
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hsstep, hWsub⟩ := toStrictMap_rel.mp (hg p hp)
    exact φ.up_mem hφW hsstep hWsub
  · rintro ⟨hMmem, hgφ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    have hφL : φ.mem (sstepFun L) :=
      (mem_sstepFun_iff φ hL).mpr (fun p hp => toStrictMap_rel.mp (hgφ p hp))
    refine ⟨sstepFun L, hφL, φ.sub hφL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨φ.sub (toStrictMap_rel.mp (hgφ p hp)), fun f hf => hf p hp⟩

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toElementMap_strctMap (ψ : (funSpace V₀ V₁).Element) :
    strctMap.toElementMap ψ = strct ψ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨M, hψM, _, hstrct⟩
    obtain ⟨hWmem, hg⟩ := hstrct
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hstepmem, hMsub⟩ := (hg p hp).1
    exact ⟨ψ.up_mem hψM hstepmem hMsub, (hg p hp).2⟩
  · rintro ⟨hWmem, hgψ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    have hψL : ψ.mem (stepFun L) :=
      (mem_stepFun_iff ψ hL).mpr (fun p hp => (hgψ p hp).1)
    refine ⟨stepFun L, hψL, ψ.sub hψL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨⟨ψ.sub (hgψ p hp).1, fun f hf => hf p hp⟩, (hgψ p hp).2⟩

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toFilter_toApproxMap (ψ : (funSpace V₀ V₁).Element) : toFilter (toApproxMap ψ) = ψ :=
  (funSpaceEquiv V₀ V₁).symm_apply_apply ψ

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ :=
  (strictFunEquiv V₀ V₁).symm_apply_apply φ

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem strct_incl (φ : (strictFun V₀ V₁).Element) : strct (incl φ) = φ := by
  show toStrictFilter (strictify (toApproxMap (toFilter (toStrictMap φ).1))) = φ
  rw [toApproxMap_toFilter,
    show strictify (toStrictMap φ).1 = toStrictMap φ from
      Subtype.ext (strictifyMap_of_isStrict (toStrictMap φ).2)]
  exact toStrictFilter_toStrictMap φ

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem strctMap_comp_inclMap :
    (strctMap (V₀ := V₀) (V₁ := V₁)).comp inclMap = idMap (strictFun V₀ V₁) := by
  apply ext_of_principal
  intro X hX
  rw [toElementMap_comp, toElementMap_inclMap, toElementMap_strctMap, strct_incl, toElementMap_idMap]

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem toStrictMap_toStrictFilter (g : StrictMap V₀ V₁) : toStrictMap (toStrictFilter g) = g :=
  (strictFunEquiv V₀ V₁).apply_symm_apply g

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem incl_strct_le (ψ : (funSpace V₀ V₁).Element) : incl (strct ψ) ≤ ψ := by
  have key : incl (strct ψ) = toFilter (strictifyMap (toApproxMap ψ)) := by
    show toFilter (toStrictMap (strct ψ)).1 = toFilter (strictifyMap (toApproxMap ψ))
    rw [show toStrictMap (strct ψ) = strictify (toApproxMap ψ) from toStrictMap_toStrictFilter _]
    rfl
  rw [key]
  conv_rhs => rw [← toFilter_toApproxMap ψ]
  exact (funSpaceEquiv V₀ V₁).symm.monotone (strictifyMap_le (toApproxMap ψ))

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem inclMap_comp_strctMap_le :
    (inclMap (V₀ := V₀) (V₁ := V₁)).comp strctMap ≤ idMap (funSpace V₀ V₁) := by
  rw [le_iff_toElementMap_le]
  intro ψ
  rw [toElementMap_comp, toElementMap_strctMap, toElementMap_inclMap, toElementMap_idMap]
  exact incl_strct_le ψ

end Part5
end Exercise627
end

section
namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 6.27 (5).** `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` for all `𝒟, ℰ` (choice-free). -/
theorem strictFun_trianglelefteq_funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    strictFun V₀ V₁ ⊴ funSpace V₀ V₁ :=
  trianglelefteq_of_projectionPair inclMap strctMap strctMap_comp_inclMap inclMap_comp_strctMap_le

end Part5
end Exercise627
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise627
section
set_option linter.unusedVariables false

theorem example_627.{u_1, u_2} : And
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
  (@And.intro
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁))
    (@And.intro
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt)))
      (@And.intro
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
        (@And.intro
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁))
          DomainTheory.NeighbourhoodSystems.Exercise627.otimes_trianglelefteq_prod
          @DomainTheory.NeighbourhoodSystems.Exercise627.inl_trianglelefteq_oplus)
        DomainTheory.NeighbourhoodSystems.Exercise627.fst_trianglelefteq_prod)
      DomainTheory.NeighbourhoodSystems.Exercise627.not_trianglelefteq_otimes)
    @DomainTheory.NeighbourhoodSystems.Exercise627.oplus_trianglelefteq_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise627.strictFun_trianglelefteq_funSpace
end

end DomainTheory.NeighbourhoodSystems.Exercise627
end

section
-- Theorem614/Setup.lean
universe w

namespace DomainTheory.NeighbourhoodSystems
namespace Theorem614

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {α : Type w}

/-- The hypotheses of Theorem 6.14, bundled: a functor `T` that is continuous on maps, monotone and
continuous on domains, together with a generating system `Γ` over a token type `Tok` such that
`{Γ} ◁ T({Γ})` (the carrier of `T({Γ})` is identified with `Tok` by `ceq`, and `hsub` is Scott's
`{Γ} ◁ T({Γ})`). -/
structure Setup where
  /-- The functor. -/
  T : Endofunctor DomainObj.{w}
  /-- `T` is continuous on maps (Definition 6.8). -/
  hmaps : ContinuousOnMaps T
  /-- `T` is monotone on domains (Definition 6.13). -/
  hmono : MonotoneOnDomains T
  /-- `T` is continuous on domains (Definition 6.13). -/
  hcont : ContinuousOnDomains T
  {Tok : Type w}
  /-- The generating system `{Γ}`. -/
  Γ : NeighborhoodSystem Tok
  /-- `T({Γ})` is a system over the same token type. -/
  ceq : (T.obj ⟨Tok, Γ⟩).carrier = Tok
  /-- Scott's hypothesis `{Γ} ◁ T({Γ})`. -/
  hsub : Γ ◁ (ceq ▸ (T.obj ⟨Tok, Γ⟩).sys : NeighborhoodSystem Tok)

end Theorem614
end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Membership in a transported system: `(e ▸ V).mem X ↔ V.mem (e.symm ▸ X)`. -/
theorem mem_cast {β : Type w} (e : β = α) (V : NeighborhoodSystem β) (X : Set α) :
    (e ▸ V : NeighborhoodSystem α).mem X ↔ V.mem (e.symm ▸ X : Set β) := by
  cases e; rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Transport composition for neighbourhood systems: `e' ▸ (e ▸ x) = (e.trans e') ▸ x`. -/
theorem rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (x : NeighborhoodSystem β) :
    (e' ▸ (e ▸ x : NeighborhoodSystem γ) : NeighborhoodSystem α) = (e.trans e') ▸ x := by
  cases e; cases e'; rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Transport composition for sets: `e' ▸ (e ▸ X) = (e.trans e') ▸ X`. -/
theorem set_rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (X : Set β) :
    (e' ▸ (e ▸ X : Set γ) : Set α) = (e.trans e') ▸ X := by
  cases e; cases e'; rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Transport a subsystem relation `D ◁ E` along a carrier-type equality `β = α`. Choice-free. -/
theorem subsystem_cast {β : Type w} (e : β = α) {D E : NeighborhoodSystem β} (h : D ◁ E) :
    (e ▸ D : NeighborhoodSystem α) ◁ (e ▸ E : NeighborhoodSystem α) := by
  cases e; exact h

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The iterated tower, as data: at level `n`, the system `Tⁿ({Γ})` over `Tok`, the carrier
identification `(T.obj Tⁿ({Γ})).carrier = Tok`, and the subdomain relation `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`
(where `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`). The successor step uses
*monotone on domains* (`MonotoneAt`) to obtain the next carrier identification and subdomain
relation. Choice-free. -/
def iter (s : Setup.{w}) : (n : ℕ) →
    Σ' (S : NeighborhoodSystem s.Tok), Σ' (ceq : (s.T.obj ⟨s.Tok, S⟩).carrier = s.Tok),
      S ◁ (ceq ▸ (s.T.obj ⟨s.Tok, S⟩).sys : NeighborhoodSystem s.Tok)
  | 0 => ⟨s.Γ, s.ceq, s.hsub⟩
  | (n + 1) =>
      let p := iter s n
      ⟨p.2.1 ▸ (s.T.obj ⟨s.Tok, p.1⟩).sys,
        (s.hmono p.2.2).carrier_eq.trans p.2.1,
        by
          have hsub := subsystem_cast p.2.1 (s.hmono p.2.2).sub
          rwa [rec_trans] at hsub⟩

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `Tⁿ({Γ})`, the `n`-th system in the tower (over `Tok`). -/
def Dsys (s : Setup.{w}) (n : ℕ) : NeighborhoodSystem s.Tok := (iter s n).1

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The carrier identification `(T.obj Tⁿ({Γ})).carrier = Tok`. -/
theorem Dceq (s : Setup.{w}) (n : ℕ) : (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier = s.Tok := (iter s n).2.1

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The basic subdomain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. -/
theorem Dchain (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ Dsys s (n + 1) := (iter s n).2.2

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Every system in the tower has the same master `Δ = Γ`. -/
theorem Dsys_master (s : Setup.{w}) (n : ℕ) : (Dsys s n).master = s.Γ.master := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← (Dchain s k).master_eq]; exact ih

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`. -/
theorem Dsys_succ (s : Setup.{w}) (n : ℕ) :
    Dsys s (n + 1) = (Dceq s n ▸ (s.T.obj ⟨s.Tok, Dsys s n⟩).sys : NeighborhoodSystem s.Tok) :=
  rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem chain_le (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) : Dsys s n ◁ Dsys s m := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (Dchain s _)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- **The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`** as a neighbourhood system over `Tok`: a set is a neighbourhood
of `𝒟` exactly when it is a neighbourhood of some `Tⁿ({Γ})`. Closure under consistent intersection
uses that the tower is a chain (`chain_le`): any finite collection of neighbourhoods sits inside one
level `Tᴺ({Γ})`, whose own `inter_mem` finishes the job. -/
def colim (s : Setup.{w}) : NeighborhoodSystem s.Tok where
  mem X := ∃ n, (Dsys s n).mem X
  master := s.Γ.master
  master_nonempty := s.Γ.master_nonempty
  master_mem := ⟨0, s.Γ.master_mem⟩
  inter_mem := by
    rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
    set N := max n (max m p) with hN
    have hXN : (Dsys s N).mem X := (chain_le s (le_max_left n _)).sub hX
    have hYN : (Dsys s N).mem Y :=
      (chain_le s ((le_max_left m p).trans (le_max_right n _))).sub hY
    have hZN : (Dsys s N).mem Z :=
      (chain_le s ((le_max_right m p).trans (le_max_right n _))).sub hZ
    exact ⟨N, (Dsys s N).inter_mem hXN hYN hZN hsub⟩
  sub_master := by
    rintro X ⟨n, hX⟩
    rw [← Dsys_master s n]
    exact (Dsys s n).sub_master hX

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

@[simp] theorem mem_colim (s : Setup.{w}) {X : Set s.Tok} :
    (colim s).mem X ↔ ∃ n, (Dsys s n).mem X := Iff.rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

@[simp] theorem colim_master (s : Setup.{w}) : (colim s).master = s.Γ.master := rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem Dsys_sub_colim (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ colim s where
  master_eq := by rw [colim_master, Dsys_master]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (Dsys s (max n m)).mem (X ∩ Y) := by
      have hle : (Dsys s m) ◁ (Dsys s (max n m)) := chain_le s (le_max_right n m)
      exact hle.sub hXY
    -- pull `X ∩ Y` back into `Tⁿ({Γ})` using consistency-in-the-bigger-level
    exact (chain_le s (le_max_left n m)).inter_closed hX hY hN

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The carrier identification `(T.obj 𝒟).carrier = Tok`, from `MonotoneAt` of `T⁰({Γ}) ◁ 𝒟`. -/
theorem colimCeq (s : Setup.{w}) : (s.T.obj ⟨s.Tok, colim s⟩).carrier = s.Tok :=
  (s.hmono (Dsys_sub_colim s 0)).carrier_eq.trans (Dceq s 0)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `T(𝒟)`, the image of the colimit, as a system over `Tok` (via `colimCeq`). -/
def Tcolim (s : Setup.{w}) : NeighborhoodSystem s.Tok :=
  colimCeq s ▸ (s.T.obj ⟨s.Tok, colim s⟩).sys

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `Tⁿ⁺¹({Γ}) ◁ T(𝒟)`: applying *monotone on domains* to `Tⁿ({Γ}) ◁ 𝒟` and transporting. -/
theorem Dsys_sub_Tcolim (s : Setup.{w}) (n : ℕ) : Dsys s (n + 1) ◁ Tcolim s := by
  have h := subsystem_cast (Dceq s n) (s.hmono (Dsys_sub_colim s n)).sub
  rw [rec_trans] at h
  exact h

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `T(𝒟)` and `𝒟` share the master `Δ = Γ`. -/
theorem Tcolim_master (s : Setup.{w}) : (Tcolim s).master = s.Γ.master := by
  rw [← (Dsys_sub_Tcolim s 0).master_eq, Dsys_master]

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- **The continuity step (the hard half of `T(𝒟) = 𝒟`).** Every neighbourhood of `T(𝒟)` is a
neighbourhood of `𝒟`. This is exactly Scott's `T(𝒟) = T(⋃ₙ Tⁿ({Γ})) = ⋃ₙ Tⁿ⁺¹({Γ}) = 𝒟`,
obtained from *continuity on domains* applied to the directed family `{Tⁿ({Γ})}`. -/
theorem Tcolim_sub_colim (s : Setup.{w}) {X : Set s.Tok} (hX : (Tcolim s).mem X) :
    (colim s).mem X := by
  obtain ⟨hmono', hC⟩ := s.hcont
  set ℱ : Set (NeighborhoodSystem s.Tok) := Set.range (Dsys s) with hℱdef
  have hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ colim s := by rintro D ⟨n, rfl⟩; exact Dsys_sub_colim s n
  have hne : ℱ.Nonempty := ⟨Dsys s 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ◁ ·) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨Dsys s (max n m), ⟨max n m, rfl⟩,
      chain_le s (le_max_left n m), chain_le s (le_max_right n m)⟩
  have hU : ∀ Y, (colim s).mem Y ↔ ∃ D ∈ ℱ, D.mem Y := by
    intro Y; constructor
    · rintro ⟨n, hn⟩; exact ⟨Dsys s n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  have heq := hC ℱ hℱ hne hdir (Subsystem.refl (colim s)) hU
  set Y₀ : Set (s.T.obj ⟨s.Tok, colim s⟩).carrier := (colimCeq s).symm ▸ X with hY₀
  -- `X ∈ T(𝒟)` says `Y₀ ∈ targetFam (refl 𝒟)` = the neighbourhood family of `T(𝒟)`.
  have hmem : Y₀ ∈ targetFam s.T hmono' (Subsystem.refl (colim s)) :=
    (mem_cast (colimCeq s) _ X).mp hX
  rw [heq, Set.mem_iUnion] at hmem
  obtain ⟨D, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hD, hmemD⟩ := hmem
  obtain ⟨n, rfl⟩ := hD
  simp only [targetFam, Set.mem_ofPred_eq] at hmemD
  -- conclude `X ∈ Tⁿ⁺¹({Γ}) ⊆ 𝒟`.
  refine ⟨n + 1, ?_⟩
  rw [Dsys_succ s n, mem_cast (Dceq s n)]
  have key : ((Dceq s n).symm ▸ X : Set (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier)
      = (s.hmono (hℱ ⟨n, rfl⟩)).carrier_eq ▸ Y₀ := by
    rw [hY₀, set_rec_trans]
  rw [key]
  exact hmemD

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The easy half of `T(𝒟) = 𝒟`: every neighbourhood of `𝒟` is a neighbourhood of `T(𝒟)`
(`𝒟 ⊆ T(𝒟)`), since `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ}) ◁ T(𝒟)`. -/
theorem colim_sub_Tcolim (s : Setup.{w}) {X : Set s.Tok} (hX : (colim s).mem X) :
    (Tcolim s).mem X := by
  obtain ⟨n, hn⟩ := hX
  exact (Dsys_sub_Tcolim s n).sub ((Dchain s n).sub hn)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- **`T(𝒟) = 𝒟`** (Scott's `𝒟 = T(𝒟)`): the two systems have the same neighbourhoods (mutual
inclusion via `colim_sub_Tcolim`/`Tcolim_sub_colim`) and the same master. -/
theorem Tcolim_eq_colim (s : Setup.{w}) : Tcolim s = colim s :=
  NeighborhoodSystem.ext
    (fun _ => ⟨fun h => Tcolim_sub_colim s h, fun h => colim_sub_Tcolim s h⟩)
    (by rw [Tcolim_master, colim_master])

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- A `DomainObj` equality from a carrier equality and a transported-system equality. -/
theorem domainObj_ext {c : Type w} (σ : NeighborhoodSystem c) (e : c = α)
    {V : NeighborhoodSystem α} (h : (e ▸ σ : NeighborhoodSystem α) = V) :
    (⟨c, σ⟩ : DomainObj) = ⟨α, V⟩ := by
  cases e; cases h; rfl

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- **`T(𝒟) ≅ 𝒟` is the identity**, packaged as a `DomainObj` equality `T(𝒟) = 𝒟`. -/
theorem colimObj_eq (s : Setup.{w}) :
    s.T.obj ⟨s.Tok, colim s⟩ = (⟨s.Tok, colim s⟩ : DomainObj) :=
  domainObj_ext (s.T.obj ⟨s.Tok, colim s⟩).sys (colimCeq s) (Tcolim_eq_colim s)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The identity isomorphism induced by an object equality in any category. -/
def isoOfEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨(𝟙 X), (𝟙 X), CategoryTheory.Category.id_comp _, CategoryTheory.Category.id_comp _⟩

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The isomorphism `T(𝒟) ≅ 𝒟` making `𝒟` a `T`-algebra (the identity, since `T(𝒟) = 𝒟`). -/
def colimIso (s : Setup.{w}) : Iso (s.T.obj ⟨s.Tok, colim s⟩) (⟨s.Tok, colim s⟩ : DomainObj) :=
  isoOfEq (colimObj_eq s)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `ρₙ = iₙ ∘ jₙ : 𝒟 → 𝒟`, the retraction onto `Tⁿ({Γ})` (Proposition 6.12's projection pair for
`Tⁿ({Γ}) ◁ 𝒟`). -/
def rho (s : Setup.{w}) (n : ℕ) : ApproximableMap (colim s) (colim s) :=
  (Dsys_sub_colim s n).inj.comp (Dsys_sub_colim s n).proj

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- Scott's relational description `X ρₙ Y ↔ ∃ z ∈ Tⁿ({Γ}), X ⊆ z ⊆ Y`. -/
theorem rho_rel (s : Setup.{w}) (n : ℕ) {X Y : Set s.Tok} :
    (rho s n).rel X Y ↔
      (colim s).mem X ∧ (colim s).mem Y ∧ ∃ z, (Dsys s n).mem z ∧ X ⊆ z ∧ z ⊆ Y := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, ⟨hcX, hDz, hXz⟩, _, hcY, hzY⟩
    exact ⟨hcX, hcY, z, hDz, hXz, hzY⟩
  · rintro ⟨hcX, hcY, z, hDz, hXz, hzY⟩
    exact ⟨z, ⟨hcX, hDz, hXz⟩, hDz, hcY, hzY⟩

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- `ρₙ ⊆ ρₘ` for `n ≤ m` (the projection chain is increasing). -/
theorem rho_mono (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) {X Y : Set s.Tok}
    (hr : (rho s n).rel X Y) : (rho s m).rel X Y := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcX, hcY, z, hDz, hXz, hzY⟩ := hr
  exact ⟨hcX, hcY, z, (chain_le s h).sub hDz, hXz, hzY⟩

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}

/-- The pointwise union `⋃ₙ ρₙ` (directed, since the chain is increasing). -/
def iSupRho (s : Setup.{w}) : ApproximableMap (colim s) (colim s) :=
  iSupMap (rho s) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono s (le_max_left i j) h,
    fun _ _ h => rho_mono s (le_max_right i j) h⟩)

end Theorem614
end

section
universe w

namespace Theorem614

variable {α : Type w}


/-- The colimit `𝒟` as a `T`-algebra, with structure map the iso `T(𝒟) → 𝒟`. -/
abbrev colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩


/-- The colimit `𝒟` as a category object `⟨Tok, 𝒟⟩`. -/
abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

/-- The `n`-th tower system `Tⁿ({Γ})` as a category object `⟨Tok, Tⁿ({Γ})⟩`. -/
abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

/-- `T(ρₙ)` as an endomorphism of `T(𝒟)`, with the category objects pinned (they cannot be inferred
from `rho s n`'s `ApproximableMap` type alone). -/
abbrev Tmap_rho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- Two algebra homomorphisms with equal underlying maps are equal (the commuting square is a
`Prop`). -/
theorem algHom_ext {Obj : Type*} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}
    {g g' : AlgHom A B} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- In the category of domains, `⊚` (categorical composition) is `ApproximableMap.comp`. -/
theorem cat_comp_eq {X Y Z : DomainObj} (g : (Y ⟶ Z)) (f : (X ⟶ Y)) :
    g ⊚ f = g.comp f := rfl

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`⋃ₙ ρₙ = I_𝒟`** (Scott's key identity for uniqueness). The forward inclusion uses
`X ⊆ z ⊆ Y ⟹ X ⊆ Y`; the reverse factors the identity step `X ⊆ X ⊆ Y` through the level
witnessing `X ∈ 𝒟`. -/
theorem iSupRho_eq_id (s : Setup.{w}) : iSupRho s = idMap (colim s) := by
  apply ApproximableMap.ext
  intro X Y
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcX, hcY, z, _, hXz, hzY⟩ := hr
    exact ⟨hcX, hcY, hXz.trans hzY⟩
  · rintro ⟨hcX, hcY, hXY⟩
    obtain ⟨n, hX⟩ := hcX
    exact ⟨n, (rho_rel s n).mpr ⟨⟨n, hX⟩, hcY, X, hX, subset_rfl, hXY⟩⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- Conjugation by the identity isomorphism `isoOfEq e` is the object-transport along `e`. -/
theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : (X ⟶ X)) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : (Y ⟶ Y)) := by
  cases e
  change (𝟙 X) ⊚ f ⊚ (𝟙 X) = f
  dsimp only [compAfter]
  rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **The carrier-transport core of `T(ρₙ) = ρₙ₊₁`.** Given the *monotone-on-domains* data for a
subsystem (its injection `Tmi`/projection `Tmj` are heterogeneously equal to the canonical 6.12 pair
`sub.inj`/`sub.proj` of the image subsystem `sub : Ps ◁ ce ▸ Qs`), the composite `Tmi ∘ Tmj` is —
after carrying the functor-image carriers `Pc, Qc` down to `Tok` — exactly the projection
`iₙ₊₁ ∘ jₙ₊₁` of the next subsystem `hsub' : Dn1 ◁ Col`. Proved by `subst`ing the carrier equalities,
after which proof-irrelevance identifies the two subsystem proofs. -/
theorem map_comp_proj_heq {Tok : Type w} {Pc Qc : Type w} (cn : Pc = Tok) (cc : Qc = Tok)
    {Ps : NeighborhoodSystem Pc} {Qs : NeighborhoodSystem Qc} (ce : Qc = Pc)
    (sub : Ps ◁ (ce ▸ Qs : NeighborhoodSystem Pc))
    {Dn1 Col : NeighborhoodSystem Tok}
    (hDn1 : (cn ▸ Ps : NeighborhoodSystem Tok) = Dn1)
    (hCol : (cc ▸ Qs : NeighborhoodSystem Tok) = Col)
    (hsub' : Dn1 ◁ Col)
    (Tmi : ApproximableMap Ps Qs) (Tmj : ApproximableMap Qs Ps)
    (hi : HEq Tmi sub.inj) (hj : HEq Tmj sub.proj) :
    HEq (Tmi.comp Tmj) (hsub'.inj.comp hsub'.proj) := by
  subst cn
  subst cc
  obtain rfl := hDn1
  obtain rfl := hCol
  have e1 : Tmi = sub.inj := eq_of_heq hi
  have e2 : Tmj = sub.proj := eq_of_heq hj
  rw [e1, e2]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`T(ρₙ) = ρₙ₊₁`, heterogeneously.** The image `T(ρₙ)` of the `n`-th projection, living over
`T(𝒟)`'s carrier, is heterogeneously equal to the `(n+1)`-st projection `ρₙ₊₁` over `Tok`. -/
theorem map_rho_heq (s : Setup.{w}) (n : ℕ) :
    HEq (Tmap_rho s n) (rho s (n + 1)) := by
  have hcomp : Tmap_rho s n
      = (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj).comp
          (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj) :=
    s.T.map_comp (X := objColim s) (Y := objDsys s n) (Z := objColim s)
      (Dsys_sub_colim s n).inj (Dsys_sub_colim s n).proj
  rw [hcomp]
  exact map_comp_proj_heq (Dceq s n) (colimCeq s) (s.hmono (Dsys_sub_colim s n)).carrier_eq
    (s.hmono (Dsys_sub_colim s n)).sub (Dsys_succ s n).symm (Tcolim_eq_colim s)
    (Dsys_sub_colim s (n + 1)) (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj)
    (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj)
    (s.hmono (Dsys_sub_colim s n)).inj_heq (s.hmono (Dsys_sub_colim s n)).proj_heq

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


theorem nonempty_strict_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (colimAlg s) B // IsStrict g.hom} :=
  nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


theorem nonempty_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty (AlgHom (colimAlg s) B) :=
  (nonempty_strict_algHom s B hk).map (·.1)

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/- concordance: source L3861 THEOREM 6.14 existence of initial algebras -/
/-- **Theorem 6.14 (Scott 1981, PRG-19) — the canonical fixed point.** Under the hypotheses
(continuous on maps, monotone and continuous on domains, with a generating set `{Γ} ◁ T({Γ})`), the
iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra whose structure map is an isomorphism
`T(𝒟) ≅ 𝒟` (the identity, since `T(𝒟) = 𝒟`), and there is a homomorphism from `𝒟` into every
`T`-algebra with a strict structure map (Theorem 6.9). This is Scott's *existence* of the initial
`T`-algebra. -/
theorem exists_algebra_with_hom (s : Setup.{w}) :
    ∃ A : TAlgebra s.T, Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
      ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B) :=
  ⟨colimAlg s, ⟨colimIso s⟩, fun B hk => nonempty_algHom s B hk⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- For a strict map `g`, `g(⊥) = ⊥` relationally: `g` sends `Δ` only to `Δ`. -/
theorem strict_rel_master {β₀ β₁ : Type w} {V₀ : NeighborhoodSystem β₀}
    {V₁ : NeighborhoodSystem β₁} {g : ApproximableMap V₀ V₁} (hg : IsStrict g) {Z : Set β₁} :
    g.rel V₀.master Z ↔ Z = V₁.master :=
  ⟨fun h => hg h, fun h => h ▸ g.master_rel⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- For a strict homomorphism `g`, the base `g ∘ ρ₀` is the least map: it relates `X` only to the
master of `E`, independent of `g`. -/
theorem gcomp_rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g : ApproximableMap (colim s) B.carrier.sys} (hg : IsStrict g)
    {X : Set s.Tok} {Z : Set B.carrier.carrier} :
    (g.comp (rho s 0)).rel X Z ↔ (colim s).mem X ∧ Z = B.carrier.sys.master := by
  rw [comp_rel]
  constructor
  · rintro ⟨Y, hrho, hgYZ⟩
    rw [rho_zero_rel s hΓ] at hrho
    obtain ⟨hcX, rfl⟩ := hrho
    exact ⟨hcX, (strict_rel_master hg).mp hgYZ⟩
  · rintro ⟨hcX, rfl⟩
    exact ⟨(colim s).master, (rho_zero_rel s hΓ).mpr ⟨hcX, rfl⟩, g.master_rel⟩

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- The base case of `g`-independence: any two strict maps agree after `∘ ρ₀`. -/
theorem gcomp_rho_zero_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g g' : ApproximableMap (colim s) B.carrier.sys}
    (hg : IsStrict g) (hg' : IsStrict g') :
    g.comp (rho s 0) = g'.comp (rho s 0) := by
  apply ApproximableMap.ext
  intro X Z
  rw [gcomp_rho_zero_rel s hΓ B hg, gcomp_rho_zero_rel s hΓ B hg']

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- Transport of a `Hom X X` along an object equality is heterogeneously equal to itself. -/
theorem transport_heq {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : (X ⟶ X)) : HEq (e ▸ f : (Y ⟶ Y)) f := by
  cases e; rfl

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ Tmap_rho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (Tmap_rho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (Tmap_rho s n)).symm

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ = i∘T(ρₙ)∘j`) and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  show g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) :=
          CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv) (colimIso s).hom g.hom
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          (CategoryTheory.Category.assoc (Tmap_rho s n ⊚ (colimIso s).inv)
            (s.T.map (X := objColim s) (Y := B.carrier) g.hom) B.str).symm
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ Tmap_rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (CategoryTheory.Category.assoc (colimIso s).inv (Tmap_rho s n)
              (s.T.map (X := objColim s) (Y := B.carrier) g.hom))
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **`g`-independence of `gₙ = g ∘ ρₙ`.** For any two strict homomorphisms into the same algebra,
`g ∘ ρₙ = g' ∘ ρₙ` for all `n` — the sequence is determined by the recursion, not by `g`. -/
theorem gcomp_rho_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) (n : ℕ) :
    g.hom.comp (rho s n) = g'.hom.comp (rho s n) := by
  induction n with
  | zero => exact gcomp_rho_zero_indep s hΓ B hg hg'
  | succ k ih => rw [gcomp_rho_succ s B g k, gcomp_rho_succ s B g' k, ih]

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **The underlying maps of two strict homomorphisms coincide**: `g = g ∘ I = g ∘ ⋃ₙ ρₙ =
⋃ₙ (g ∘ ρₙ)`, and the latter is `g`-independent. -/
theorem gcomp_eq (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) :
    g.hom = g'.hom := by
  have key : g.hom.comp (iSupRho s) = g'.hom.comp (iSupRho s) := by
    apply ApproximableMap.ext
    intro X Z
    rw [comp_rel, comp_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g'.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [← gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
  have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap g.hom
  have e' : g'.hom.comp (idMap (colim s)) = g'.hom := comp_idMap g'.hom
  rw [← e, ← e', ← iSupRho_eq_id]
  exact key

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **Uniqueness of strict homomorphisms out of `𝒟`.** Any two strict `T`-algebra homomorphisms from
the canonical solution into the same algebra are equal. -/
theorem algHom_unique (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) : g = g' :=
  algHom_ext (gcomp_eq s hΓ B g g' hg hg')

end Theorem614
end

section
universe w

namespace Theorem614


variable {α : Type w}


/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a *unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ` projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem614
section
set_option linter.unusedVariables false

theorem theorem_614.{w} : And
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g)) :=
  @And.intro
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    ∃ (A :
      @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
      And
        (Nonempty.{w + 1}
          (@DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A))
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
              DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A)))
        (∀
          (B :
            @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
          @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
              (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
            Nonempty.{w + 1}
              (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T A B)))
  (∀ (s : DomainTheory.NeighbourhoodSystems.Theorem614.Setup.{w}),
    (∀ (X : Set.{w} s.Tok),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem.{w} s.Tok s.Γ X →
          @Eq.{w + 1} (Set.{w} s.Tok) X (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master.{w} s.Tok s.Γ)) →
      ∀
        (B :
          @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T),
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).carrier
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
            (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B)).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
            (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B) →
          ∃ (g :
            @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
              (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
            And
              (@DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                  (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g))
              (∀
                (g' :
                  @DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                    (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B),
                @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{w, w}
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).carrier
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                        (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s)).sys
                    (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T B).sys
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B g') →
                  @Eq.{w + 1}
                    (@DomainTheory.NeighbourhoodSystems.AlgHom.{w + 1, w}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{w}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} s.T
                      (DomainTheory.NeighbourhoodSystems.Theorem614.colimAlg.{w} s) B)
                    g' g))
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_algebra_with_hom.{w}
  DomainTheory.NeighbourhoodSystems.Theorem614.exists_unique_strict_algHom.{w}
end

end DomainTheory.NeighbourhoodSystems.Theorem614
namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

/-- `subFam E` is non-empty: `E` itself is a subsystem (`Subsystem.refl`), so its own
neighbourhood-set `{X ∣ E.mem X}` is a member. -/
theorem subFam_nonempty (E : NeighborhoodSystem α) : (subFam E).Nonempty :=
  ⟨{X | E.mem X}, E, Subsystem.refl E, rfl⟩
end

section
variable {α : Type*}

/-- **Closure under non-empty intersection** (Exercise 2.22's hypothesis (i)). -/
theorem subFam_sInter_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : ⋂₀ ℱ ∈ subFam E :=
  ⟨interSys E ℱ hne hℱ, interSys_subsystem E ℱ hne hℱ, (interSys_nbset E ℱ hne hℱ).symm⟩
end

section
variable {α : Type*}

/-- **The poset of subsystems is the family `subFam E`.** The subsystems of `E`, ordered by `◁`,
are order-isomorphic to `subFam E` ordered by `⊆`. A subsystem is sent to its family of
neighbourhoods `{X ∣ D.mem X}`, and recovered by `ofMem`; order is preserved and reflected by
Scott's remark `Subsystem.subsystem_iff_subset_of_common`. -/
def subIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o {𝒮 : Set (Set α) // 𝒮 ∈ subFam E} where
  toFun D := ⟨{X | D.1.mem X}, ⟨D.1, D.2, rfl⟩⟩
  invFun 𝒮 := ⟨ofMem E 𝒮.1 𝒮.2, ofMem_subsystem E 𝒮.1 𝒮.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    apply NeighborhoodSystem.ext
    · intro X; exact Iff.rfl
    · exact D.2.master_eq.symm
  right_inv := by
    intro 𝒮
    apply Subtype.ext
    ext X
    exact Iff.rfl
  map_rel_iff' := by
    intro a b
    show ({X | a.1.mem X} : Set (Set α)) ⊆ {X | b.1.mem X} ↔ a.1 ◁ b.1
    constructor
    · intro hsub
      refine (Subsystem.subsystem_iff_subset_of_common a.2 b.2).mpr ?_
      intro X hX
      exact hsub hX
    · intro hsub X hX
      exact hsub.sub hX
end

end DomainTheory.NeighbourhoodSystems.Proposition611
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example62C in
/-- Every neighbourhood of the three-way separated sum `sum3` is non-empty (so `sum3` is again an
object of the `∅`-free category). -/
theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- The right-hand side of Scott's domain equation: the sum system `D + (D^§ × D^§)`. -/
def sumSys : NeighborhoodSystem (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α)))) :=
  sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of the sum `D + (D^§ × D^§)` is empty. -/
theorem sumSys_mem_nonempty {W : Set (Option (α ⊕ ((List Bool × α) ⊕ (List Bool × α))))}
    (h : (sumSys D hD).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (hD X hX)
  · exact inj₁_nonempty (prod_dsharp_nonempty D hD Y hY)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- A sum-neighbourhood of the form `0X` arises only from the left factor, so `X ∈ 𝒟`. -/
theorem sum_mem_inj₀_inv {X : Set α} (h : (sumSys D hD).mem (inj₀ X)) : D.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- A sum-neighbourhood of the form `1V` arises only from the right factor, so `V ∈ 𝒟^§ × 𝒟^§`. -/
theorem sum_mem_inj₁_inv {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    (h : (sumSys D hD).mem (inj₁ V)) : (prod (Dsharp D hD) (Dsharp D hD)).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := hD X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Equation

end Example61
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new `T`-algebra
`(T(D), T(i))`. -/
abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The structure map `i : T(D) → D` is itself a homomorphism `(T(D), T(i)) → (D, i)`: the square
`i ∘ T(i) = i ∘ T(i)` commutes trivially. -/
def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- The composite `i ∘ j` of `i` with the descent homomorphism `j : (D,i) → (T(D),T(i))` is the
identity on `D`. -/
theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = (𝟙 A.carrier) := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  exact congrArg AlgHom.hom h
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

end

section
set_option linter.unusedVariables false

theorem theorem_67.{u, u_1} : ∀ {Obj : Type u} [inst : CategoryTheory.Category.{u_1, u} Obj]
  {T : @DomainTheory.NeighbourhoodSystems.Endofunctor Obj inst}
  (A : @DomainTheory.NeighbourhoodSystems.TAlgebra Obj inst T)
  (hA : @DomainTheory.NeighbourhoodSystems.IsInitial Obj inst T A),
  @Eq
    (@Quiver.Hom Obj (@CategoryTheory.CategoryStruct.toQuiver Obj (@CategoryTheory.Category.toCategoryStruct Obj inst))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
    (@DomainTheory.NeighbourhoodSystems.compAfter Obj inst
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj Obj inst T
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A))
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.str Obj inst T A)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom Obj inst T A (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A)
        (@DomainTheory.NeighbourhoodSystems.IsInitial.desc Obj inst T A hA
          (@DomainTheory.NeighbourhoodSystems.tStr Obj inst T A))))
    (@CategoryTheory.CategoryStruct.id Obj (@CategoryTheory.Category.toCategoryStruct Obj inst)
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier Obj inst T A)) :=
  @DomainTheory.NeighbourhoodSystems.str_comp_desc
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- The strict map represented by `⊥` of the strict function space relates `X` to `Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥` (least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- **The per-step computation of Theorem 6.9's operator.** For the operator `Op = (k ∘ · ∘ j) ∘ Φ`
on the strict function space, `Op(x)` is the strict map `k ∘ T(toStrictMap x) ∘ j`. This is the
content of `homOp_apply_filter` plus the defining property `hΦ` of the Definition 6.8 witness `Φ`. -/
theorem opStep (T : Endofunctor DomainObj.{w}) (D E : DomainObj.{w})
    (j : ApproximableMap D.sys (T.obj D).sys) (k : ApproximableMap (T.obj E).sys E.sys)
    (hj : IsStrict j) (hk : IsStrict k)
    (Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys))
    (hΦ : ∀ f : StrictMap D.sys E.sys,
      (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1)
    (x : (strictFun D.sys E.sys).Element) :
    (toStrictMap (((homOp T D E j k hj hk).comp Φ).toElementMap x)).1
      = k.comp ((T.map (X := D) (Y := E) (toStrictMap x).1).comp j) := by
  set h := toStrictMap x with hh
  have hx : toStrictFilter h = x := toStrictFilter_toStrictMap x
  have hφ : Φ.toElementMap x
      = toStrictFilter (toStrictMap (Φ.toElementMap (toStrictFilter h))) := by
    rw [← hx]; exact (toStrictFilter_toStrictMap _).symm
  rw [toElementMap_comp, hφ, homOp_apply_filter, toStrictMap_toStrictFilter]
  show k.comp ((toStrictMap (Φ.toElementMap (toStrictFilter h))).1.comp j)
      = k.comp ((T.map (X := D) (Y := E) h.1).comp j)
  rw [hΦ h]
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/- concordance: source L3713 PROPOSITION 6.7 functor preserves initiality -/
/-- **Proposition 6.7 (Lambek's lemma; Scott 1981, PRG-19).** The structure map `i : T(D) → D` of an
initial `T`-algebra is an isomorphism `T(D) ≅ D`, with inverse the descent homomorphism `j`. -/
def lambek (A : TAlgebra T) (hA : IsInitial A) : Iso (T.obj A.carrier) A.carrier where
  hom := A.str
  inv := (hA.desc (tStr A)).hom
  inv_hom_id := str_comp_desc A hA
  hom_inv_id :=
    calc (hA.desc (tStr A)).hom ⊚ A.str
        = (tStr A).str ⊚ T.map (hA.desc (tStr A)).hom := (hA.desc (tStr A)).comm
      _ = T.map A.str ⊚ T.map (hA.desc (tStr A)).hom := rfl
      _ = T.map (A.str ⊚ (hA.desc (tStr A)).hom) := (T.map_comp _ _).symm
      _ = T.map ((𝟙 A.carrier)) := by rw [str_comp_desc A hA]
      _ = (𝟙 (T.obj A.carrier)) := T.map_id _
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510
universe w

/- concordance: source L4015 THEOREM 6.16 initial algebra is minimal -/
/-- **Theorem 6.16 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D` is an initial
`T`-algebra, then for any system `E ≅ T(E)` we have `D ⊴ E`: the initial algebra embeds as a
subdomain of every solution of the domain equation. -/
theorem trianglelefteq_of_isInitial
    (T : Endofunctor DomainObj.{w}) (hT : ContinuousOnMaps T)
    (Dalg : TAlgebra T) (hinit : IsInitial Dalg)
    (E : DomainObj.{w}) (isoE : Iso (T.obj E) E) :
    Dalg.carrier.sys ⊴ E.sys := by
  -- Lambek (Proposition 6.7): the structure map of `D` is an isomorphism `i : T(D) ≅ D`.
  let isoD : Iso (T.obj Dalg.carrier) Dalg.carrier := lambek Dalg hinit
  -- strictness of the four structure maps (each is a split iso, hence preserves `⊥`).
  have hi : IsStrict isoD.hom := isStrict_of_comp_eq_id isoD.inv_hom_id
  have hj : IsStrict isoD.inv := isStrict_of_comp_eq_id isoD.hom_inv_id
  have hu : IsStrict isoE.hom := isStrict_of_comp_eq_id isoE.inv_hom_id
  have hv : IsStrict isoE.inv := isStrict_of_comp_eq_id isoE.hom_inv_id
  -- the iso laws in `.comp` form.
  have hji : isoD.inv.comp isoD.hom = idMap (T.obj Dalg.carrier).sys := isoD.hom_inv_id
  have hvu : isoE.inv.comp isoE.hom = idMap (T.obj E).sys := isoE.hom_inv_id
  have huv : isoE.hom.comp isoE.inv = idMap E.sys := isoE.inv_hom_id
  -- Definition 6.8 witnesses that `λf. T(f)` is approximable on each strict function space.
  obtain ⟨ΦDE, hΦDE⟩ := hT Dalg.carrier E
  obtain ⟨ΦED, hΦED⟩ := hT E Dalg.carrier
  obtain ⟨ΦEE, hΦEE⟩ := hT E E
  -- the three operators (Theorem 6.9's `λf. k ∘ T(f) ∘ j`) for `h`, `g`, `k`.
  let Oph := (homOp T Dalg.carrier E isoD.inv isoE.hom hj hu).comp ΦDE
  let Opg := (homOp T E Dalg.carrier isoE.inv isoD.hom hv hi).comp ΦED
  let Opk := (homOp T E E isoE.inv isoE.hom hv hu).comp ΦEE
  -- the approximant chains.
  let H : ℕ → ApproximableMap Dalg.carrier.sys E.sys := fun n => (toStrictMap (Oph.iterElem n)).1
  let G : ℕ → ApproximableMap E.sys Dalg.carrier.sys := fun n => (toStrictMap (Opg.iterElem n)).1
  let K : ℕ → ApproximableMap E.sys E.sys := fun n => (toStrictMap (Opk.iterElem n)).1
  -- `iterElem 0 = ⊥`.
  have iterElem_zero : ∀ {γ : Type w} {V : NeighborhoodSystem γ} (f : ApproximableMap V V),
      f.iterElem 0 = V.bot := by
    intro γ V f
    show (f.iterMap 0).toElementMap V.bot = V.bot
    rw [iterMap_zero, toElementMap_idMap]
  -- the recursion equations `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, etc.
  have H_succ : ∀ n, H (n + 1)
      = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) (H n)).comp isoD.inv) := by
    intro n
    show (toStrictMap (Oph.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE (Oph.iterElem n)
  have G_succ : ∀ n, G (n + 1)
      = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) (G n)).comp isoE.inv) := by
    intro n
    show (toStrictMap (Opg.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED (Opg.iterElem n)
  have K_succ : ∀ n, K (n + 1)
      = isoE.hom.comp ((T.map (X := E) (Y := E) (K n)).comp isoE.inv) := by
    intro n
    show (toStrictMap (Opk.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE (Opk.iterElem n)
  -- monotonicity of the chains.
  have H_mono : ∀ {n m : ℕ}, n ≤ m → H n ≤ H m := fun hnm =>
    toStrictMap_mono (iterElem_mono Oph hnm)
  have G_mono : ∀ {n m : ℕ}, n ≤ m → G n ≤ G m := fun hnm =>
    toStrictMap_mono (iterElem_mono Opg hnm)
  -- the algebraic core: `(u ∘ a ∘ j) ∘ (i ∘ b ∘ v) = u ∘ (a ∘ b) ∘ v` (uses `j ∘ i = I`).
  have key : ∀ (a : ApproximableMap (T.obj Dalg.carrier).sys (T.obj E).sys)
      (b : ApproximableMap (T.obj E).sys (T.obj Dalg.carrier).sys),
      (isoE.hom.comp (a.comp isoD.inv)).comp (isoD.hom.comp (b.comp isoE.inv))
        = isoE.hom.comp ((a.comp b).comp isoE.inv) := by
    intro a b
    rw [comp_assoc isoE.hom (a.comp isoD.inv) (isoD.hom.comp (b.comp isoE.inv)),
        comp_assoc a isoD.inv (isoD.hom.comp (b.comp isoE.inv)),
        ← comp_assoc isoD.inv isoD.hom (b.comp isoE.inv), hji, idMap_comp,
        ← comp_assoc a b isoE.inv]
  -- functoriality `T(p) ∘ T(q) = T(p ∘ q)` in `.comp` form.
  have hTcomp : ∀ (p : ApproximableMap Dalg.carrier.sys E.sys)
      (q : ApproximableMap E.sys Dalg.carrier.sys),
      (T.map (X := Dalg.carrier) (Y := E) p).comp (T.map (X := E) (Y := Dalg.carrier) q)
        = T.map (X := E) (Y := E) (p.comp q) :=
    fun p q => (T.map_comp (X := E) (Y := Dalg.carrier) (Z := E) p q).symm
  -- **the ladder**: `hₙ ∘ gₙ = kₙ`.
  have ladder : ∀ n, (H n).comp (G n) = K n := by
    intro n
    induction n with
    | zero =>
      apply ApproximableMap.ext
      intro X Z
      have hH0 : ∀ {P Q}, (H 0).rel P Q ↔ Dalg.carrier.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        show (toStrictMap (Oph.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hG0 : ∀ {P Q}, (G 0).rel P Q ↔ E.sys.mem P ∧ Q = Dalg.carrier.sys.master := by
        intro P Q
        show (toStrictMap (Opg.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hK0 : ∀ {P Q}, (K 0).rel P Q ↔ E.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        show (toStrictMap (Opk.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      constructor
      · rintro ⟨Y, hG, hHr⟩
        rw [hG0] at hG; rw [hH0] at hHr
        obtain ⟨hEX, rfl⟩ := hG
        obtain ⟨_, rfl⟩ := hHr
        rw [hK0]; exact ⟨hEX, rfl⟩
      · intro hK
        rw [hK0] at hK
        obtain ⟨hEX, rfl⟩ := hK
        exact ⟨Dalg.carrier.sys.master,
          (hG0).mpr ⟨hEX, rfl⟩, (hH0).mpr ⟨Dalg.carrier.sys.master_mem, rfl⟩⟩
    | succ n ih =>
      rw [H_succ n, G_succ n, key, K_succ n, hTcomp (H n) (G n), ih]
  -- the fixed-point maps and their `⊔`-decomposition.
  let hh := (toStrictMap Oph.fixElement).1
  let gg := (toStrictMap Opg.fixElement).1
  let kk := (toStrictMap Opk.fixElement).1
  have H_fix_rel : ∀ X Y, hh.rel X Y ↔ ∃ n, (H n).rel X Y := by
    intro X Y
    show (toStrictMap Oph.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Oph.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have G_fix_rel : ∀ X Y, gg.rel X Y ↔ ∃ n, (G n).rel X Y := by
    intro X Y
    show (toStrictMap Opg.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opg.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have K_fix_rel : ∀ X Y, kk.rel X Y ↔ ∃ n, (K n).rel X Y := by
    intro X Y
    show (toStrictMap Opk.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opk.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  -- `h ∘ g = k` (the diagonal of the doubly-indexed directed family, via the ladder).
  have hgk : hh.comp gg = kk := by
    apply ApproximableMap.ext
    intro X Z
    constructor
    · rintro ⟨Y, hgXY, hhYZ⟩
      rw [G_fix_rel] at hgXY
      rw [H_fix_rel] at hhYZ
      obtain ⟨m, hm⟩ := hgXY
      obtain ⟨n, hn⟩ := hhYZ
      rw [K_fix_rel]
      refine ⟨max m n, ?_⟩
      rw [← ladder (max m n)]
      exact ⟨Y, G_mono (le_max_left m n) X Y hm, H_mono (le_max_right m n) Y Z hn⟩
    · intro hk
      rw [K_fix_rel] at hk
      obtain ⟨p, hp⟩ := hk
      rw [← ladder p] at hp
      obtain ⟨Y, hG, hHr⟩ := hp
      exact ⟨Y, (G_fix_rel X Y).mpr ⟨p, hG⟩, (H_fix_rel Y Z).mpr ⟨p, hHr⟩⟩
  -- `k ⊑ I_E`, because `I_E` is a fixed point of `k ↦ u ∘ T(k) ∘ v`.
  have hk_le : kk ≤ idMap E.sys := by
    have hstepeq : (toStrictMap (Opk.toElementMap
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys)))).1
          = idMap E.sys := by
      have hs := opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))
      have hmapid : T.map (X := E) (Y := E) (idMap E.sys) = idMap (T.obj E).sys := T.map_id E
      rw [hs, show (toStrictMap (toStrictFilter
          (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))).1 = idMap E.sys from
          congrArg Subtype.val (toStrictMap_toStrictFilter _),
        hmapid, idMap_comp, huv]
    have hfp : Opk.toElementMap (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))
        = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
      calc Opk.toElementMap (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩)
          = toStrictFilter (toStrictMap (Opk.toElementMap
              (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩))) :=
            (toStrictFilter_toStrictMap _).symm
        _ = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
            congr 1
            apply Subtype.ext
            rw [hstepeq]
        _ = toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩ := rfl
    have hle : Opk.fixElement ≤ toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) :=
      fixElement_le_of_toElementMap_le Opk (le_of_eq hfp)
    have hmono := toStrictMap_mono hle
    show (toStrictMap Opk.fixElement).1 ≤ idMap E.sys
    refine le_of_le_of_eq hmono ?_
    exact congrArg Subtype.val (toStrictMap_toStrictFilter _)
  -- `h` and `g` are algebra homomorphisms.
  let Balg : TAlgebra T := ⟨E, isoE.hom⟩
  have h_fixeq : hh = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) hh).comp isoD.inv) := by
    have hs := opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE Oph.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have h_comm : hh.comp isoD.hom = isoE.hom.comp (T.map (X := Dalg.carrier) (Y := E) hh) := by
    conv_lhs => rw [h_fixeq]
    rw [comp_assoc, comp_assoc, hji, comp_idMap]
  let h_alg : AlgHom Dalg Balg := { hom := hh, comm := h_comm }
  have g_fixeq : gg = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) gg).comp isoE.inv) := by
    have hs := opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED Opg.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have g_comm : gg.comp isoE.hom = isoD.hom.comp (T.map (X := E) (Y := Dalg.carrier) gg) := by
    conv_lhs => rw [g_fixeq]
    rw [comp_assoc, comp_assoc, hvu, comp_idMap]
  let g_alg : AlgHom Balg Dalg := { hom := gg, comm := g_comm }
  -- `g ∘ h = I_D` by initiality of `D`.
  have hgh_id : gg.comp hh = idMap Dalg.carrier.sys := by
    have huniq : g_alg.comp h_alg = AlgHom.id Dalg := by
      rw [hinit.uniq Dalg (g_alg.comp h_alg), hinit.uniq Dalg (AlgHom.id Dalg)]
    exact congrArg AlgHom.hom huniq
  -- conclude via Lemma 6.15.
  exact trianglelefteq_of_projectionPair hh gg hgh_id (le_of_eq_of_le hgk hk_le)
end

section
set_option linter.unusedVariables false

theorem theorem_616.{w} : ∀
  (T :
    @DomainTheory.NeighbourhoodSystems.Endofunctor.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}),
  DomainTheory.NeighbourhoodSystems.ContinuousOnMaps.{w} T →
    ∀
      (Dalg :
        @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T)
      (hinit :
        @DomainTheory.NeighbourhoodSystems.IsInitial.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg)
      (E : DomainTheory.NeighbourhoodSystems.DomainObj.{w})
      (isoE :
        @DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T E)
          E),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq.{w, w}
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg).carrier
        E.carrier
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg).sys
        E.sys :=
  DomainTheory.NeighbourhoodSystems.trianglelefteq_of_isInitial.{w}
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- **The functor `T(X) = 𝟙 + X + X` on objects.** Over `D`, the system is the genuine three-way
separated sum `𝟙 + D + D` (Example 6.2's `sum3`, with `𝟙 = unitSys`), again `∅`-free by
`sum3_nonempty`. -/
abbrev tcObj (D : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Option (Unit ⊕ D.carrier ⊕ D.carrier)
  sys := sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty
  nonempty := sum3_nonempty
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem tcObj_sys (D : StrictDomainObj.{w}) :
    (tcObj D).sys = sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty := rfl
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `0`-copy `0X` is itself a `0`-copy. -/
theorem mem_subset_j0_inv {W : Set (Option (α ⊕ β ⊕ γ))} {X : Set α}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j0 X) :
    ∃ X₂, V₀.mem X₂ ∧ W = j0 X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j0
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0

end ShapeLemmas
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `1`-copy `1Y` is itself a `1`-copy. -/
theorem mem_subset_j1_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Y : Set β}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j1 Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = j1 Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · exact ⟨Y₂, hY₂, rfl⟩
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1

end ShapeLemmas
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `2`-copy `2Z` is itself a `2`-copy. -/
theorem mem_subset_j2_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Z : Set γ}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j2 Z) :
    ∃ Z₂, V₂.mem Z₂ ∧ W = j2 Z₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · exact ⟨Z₂, hZ₂, rfl⟩

end ShapeLemmas
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `0`-injection `D₀ ↪ D₀+D₁+D₂`: send `x₀∈|D₀|` to the sum element whose only proper
neighbourhoods are the `0`-copies `0X` with `X∈x₀`. -/
def sinj0 (x₀ : V₀.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ X, V₀.mem X ∧ W = j0 X ∧ x₀.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [master3_inter_j0 hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, master3_inter_j0 hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x₀.sub (x₀.inter_mem hx hx'), j0_inter_j0 X X', x₀.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', hX', rfl, x₀.up_mem hx hX' (j0_subset_j0.mp hsub)⟩
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

@[simp] theorem sinj0_mem_j0 {x₀ : V₀.Element} {X : Set α} (hX : V₀.mem X) :
    (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀).mem (j0 X) ↔ x₀.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · rw [j0_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `1`-injection `D₁ ↪ D₀+D₁+D₂`. -/
def sinj1 (x₁ : V₁.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Y, V₁.mem Y ∧ W = j1 Y ∧ x₁.mem Y
  sub := by
    rintro W (rfl | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) (rfl | ⟨Y', hY', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Y', hY', by rw [master3_inter_j1 hY'], hx'⟩
    · exact Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j1 hY], hx⟩
    · exact Or.inr ⟨Y ∩ Y', x₁.sub (x₁.inter_mem hx hx'), j1_inter_j1 Y Y', x₁.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr ⟨Y', hY', rfl, x₁.up_mem hx hY' (j1_subset_j1.mp hsub)⟩
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

@[simp] theorem sinj1_mem_j1 {x₁ : V₁.Element} {Y : Set β} (hY : V₁.mem Y) :
    (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁).mem (j1 Y) ↔ x₁.mem Y := by
  constructor
  · rintro (h0 | ⟨Y', hY', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · rw [j1_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Y, hY, rfl, hx⟩

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `2`-injection `D₂ ↪ D₀+D₁+D₂`. -/
def sinj2 (x₂ : V₂.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Z, V₂.mem Z ∧ W = j2 Z ∧ x₂.mem Z
  sub := by
    rintro W (rfl | ⟨Z, hZ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) (rfl | ⟨Z', hZ', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Z', hZ', by rw [master3_inter_j2 hZ'], hx'⟩
    · exact Or.inr ⟨Z, hZ, by rw [Set.inter_comm, master3_inter_j2 hZ], hx⟩
    · exact Or.inr ⟨Z ∩ Z', x₂.sub (x₂.inter_mem hx hx'), j2_inter_j2 Z Z', x₂.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr ⟨Z', hZ', rfl, x₂.up_mem hx hZ' (j2_subset_j2.mp hsub)⟩

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

@[simp] theorem sinj2_mem_j2 {x₂ : V₂.Element} {Z : Set γ} (hZ : V₂.mem Z) :
    (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂).mem (j2 Z) ↔ x₂.mem Z := by
  constructor
  · rintro (h0 | ⟨Z', hZ', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · rw [j2_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Z, hZ, rfl, hx⟩

end SumInj
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sinj1_mono {x x' : V₁.Element} (hx : x ≤ x') :
    sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj1 x' := by
  rintro W (rfl | ⟨Y, hY, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Y, hY, rfl, hx Y hm⟩

end SumInjMap
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sinj2_mono {x x' : V₂.Element} (hx : x ≤ x') :
    sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj2 x' := by
  rintro W (rfl | ⟨Z, hZ, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Z, hZ, rfl, hx Z hm⟩

end SumInjMap
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- **The three-way sum map `f₀ + f₁ + f₂ : 𝒟₀+𝒟₁+𝒟₂ → 𝒟₀'+𝒟₁'+𝒟₂'`.** Routes each tagged copy `iX`
through `fᵢ` (to `iYᵢ'`), and sends everything to the codomain master. (The three-way analogue of
Exercise 3.19's `sumMap`.) -/
def sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    ApproximableMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) (sum3 V₀' V₁' V₂' h₀' h₁' h₂') where
  rel W W' := (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W ∧ (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W' ∧
    (W' = master3 V₀' V₁' V₂' ∨
      (∃ X Y', W = j0 X ∧ W' = j0 Y' ∧ f₀.rel X Y') ∨
      (∃ X Y', W = j1 X ∧ W' = j1 Y' ∧ f₁.rel X Y') ∨
      (∃ X Y', W = j2 X ∧ W' = j2 Y' ∧ f₂.rel X Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem,
    Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β' ⊕ γ')),
        (W'' = master3 V₀' V₁' V₂' ∨
          (∃ X Y', W = j0 X ∧ W'' = j0 Y' ∧ f₀.rel X Y') ∨
          (∃ X Y', W = j1 X ∧ W'' = j1 Y' ∧ f₁.rel X Y') ∨
          (∃ X Y', W = j2 X ∧ W'' = j2 Y' ∧ f₂.rel X Y')) →
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩)
      · exact (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem
      · exact Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩))
    have key : (W'₁ ∩ W'₂ = master3 V₀' V₁' V₂' ∨
        (∃ X Y', W = j0 X ∧ W'₁ ∩ W'₂ = j0 Y' ∧ f₀.rel X Y') ∨
        (∃ X Y', W = j1 X ∧ W'₁ ∩ W'₂ = j1 Y' ∧ f₁.rel X Y') ∨
        (∃ X Y', W = j2 X ∧ W'₁ ∩ W'₂ = j2 Y' ∧ f₂.rel X Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩
        | ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ master3 V₀' V₁' V₂' from
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j0_subset_master3 (f₀.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := j0_injective (hWX₁.symm.trans hWX₂)
          rw [j0_inter_j0]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f₀.inter_right hf₁ hf₂⟩)
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWY₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWZ₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j1_subset_master3 (f₁.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWX₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
        · obtain rfl : Y = Y' := j1_injective (hWY₁.symm.trans hWY₂)
          rw [j1_inter_j1]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, f₁.inter_right hf₁ hf₂⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWZ₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j2_subset_master3 (f₂.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩))
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWX₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWY₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
        · obtain rfl : Z = Z' := j2_injective (hWZ₁.symm.trans hWZ₂)
          rw [j2_inter_j2]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁ ∩ Y'₂, hWZ₁, rfl, f₂.inter_right hf₁ hf₂⟩))
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hf⟩ | ⟨Z, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_master3_of_subset hW'W'₂ ((sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂mem))
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_j0_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := j0_subset_j0.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f₀.mono hf hX₂X (j0_subset_j0.mp hW'W'₂) hX₂ hY'₂⟩)
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_j1_inv hW₂mem hW₂W
      have hY₂Y : Y₂ ⊆ Y := j1_subset_j1.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y₂, Y'₂, rfl, rfl,
          f₁.mono hf hY₂Y (j1_subset_j1.mp hW'W'₂) hY₂ hY'₂⟩))
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · obtain ⟨Z₂, hZ₂, rfl⟩ := mem_subset_j2_inv hW₂mem hW₂W
      have hZ₂Z : Z₂ ⊆ Z := j2_subset_j2.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z₂, Y'₂, rfl, rfl,
          f₂.mono hf hZ₂Z (j2_subset_j2.mp hW'W'₂) hZ₂ hY'₂⟩))

end SumMap3
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- The three-way sum map is always strict: `(f₀+f₁+f₂)(⊥) = ⊥`. (The master only relates to the
master, since `master3` is not any tagged copy.) -/
theorem isStrict_sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    IsStrict (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
      f₀ f₁ f₂) := by
  rintro Y ⟨-, -, hd⟩
  have h0 : (none : Option (α ⊕ β ⊕ γ)) ∈ (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master := none_mem_master3
  rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWX ▸ h0) none_not_mem_j0
  · exact absurd (hWX ▸ h0) none_not_mem_j1
  · exact absurd (hWX ▸ h0) none_not_mem_j2

end SumMap3
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- **Functoriality (composition): `(g₀∘f₀) + (g₁∘f₁) + (g₂∘f₂) = (g₀+g₁+g₂) ∘ (f₀+f₁+f₂)`.** -/
theorem sumMap3_comp {α'' β'' γ'' : Type*} {V₀'' : NeighborhoodSystem α''}
    {V₁'' : NeighborhoodSystem β''} {V₂'' : NeighborhoodSystem γ''}
    {h₀'' : ∀ X, V₀''.mem X → X.Nonempty} {h₁'' : ∀ Y, V₁''.mem Y → Y.Nonempty}
    {h₂'' : ∀ Z, V₂''.mem Z → Z.Nonempty}
    (g₀ : ApproximableMap V₀' V₀'') (g₁ : ApproximableMap V₁' V₁'') (g₂ : ApproximableMap V₂' V₂'')
    (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁') (f₂ : ApproximableMap V₂ V₂') :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
        (g₀.comp f₀) (g₁.comp f₁) (g₂.comp f₂)
      = (sumMap3 (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
          g₀ g₁ g₂).comp
        (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
          f₀ f₁ f₂) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨X, Z'', rfl, rfl, Y', hf, hg⟩ | ⟨Y, Z'', rfl, rfl, Y', hf, hg⟩
      | ⟨Z, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨master3 V₀' V₁' V₂', ⟨hW, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, hW'', Or.inl rfl⟩
    · exact ⟨j0 Y', ⟨hW, Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩),
        Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), hW'', Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩)⟩
    · exact ⟨j1 Y', ⟨hW, Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩))⟩
    · exact ⟨j2 Y', ⟨hW, Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Z, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inr ⟨Y', Z'', rfl, rfl, hg⟩))⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, _, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨X', Z'', hW'X', rfl, hg⟩ | ⟨Y', Z'', hW'Y', rfl, hg⟩
      | ⟨Z', Z'', hW'Z', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'X'.symm) ▸ none_mem_master3) none_not_mem_j0
      · obtain rfl : Y'₀ = X' := j0_injective (hW'eq.symm.trans hW'X')
        exact Or.inr (Or.inl ⟨X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
      · obtain rfl : Y'₀ = Y' := j1_injective (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr (Or.inl ⟨Y, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Z'.symm) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · obtain rfl : Y'₀ = Z' := j2_injective (hW'eq.symm.trans hW'Z')
        exact Or.inr (Or.inr (Or.inr ⟨Z, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))

end SumMap3
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- **Functoriality (identities): `I + I + I = I`.** -/
theorem sumMap3_id :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀) (h₁' := h₁) (h₂' := h₂)
      (idMap V₀) (idMap V₁) (idMap V₂) = idMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, _, _, hXY⟩ | ⟨Y, Y', rfl, rfl, _, _, hXY⟩
      | ⟨Z, Y', rfl, rfl, _, _, hXY⟩
    · exact (sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW
    · exact j0_subset_j0.mpr hXY
    · exact j1_subset_j1.mpr hXY
    · exact j2_subset_j2.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
    · left; exact eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW')
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, X', rfl, rfl, hX, hX', j0_subset_j0.mp hsub⟩)
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hY, hY', j1_subset_j1.mp hsub⟩))
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z, Z', rfl, rfl, hZ, hZ', j2_subset_j2.mp hsub⟩))

end SumMap3
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- `(f₀+f₁+f₂)(inj₀ x) = inj₀(f₀ x)`. -/
theorem sumMap3_sinj0 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₀ : V₀.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀)
      = sinj0 (V₁ := V₁') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₀.toElementMap x₀) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · have hXX : X = X₀ := j0_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₀.rel_cod hf, rfl, ⟨X₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j0 X, Or.inr ⟨X, x₀.sub hx, rfl, hx⟩, Or.inr (Or.inl ⟨X, x₀.sub hx, rfl⟩),
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩

end SumInjMap
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- `(f₀+f₁+f₂)(inj₁ x) = inj₁(f₁ x)`. -/
theorem sumMap3_sinj1 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₁ : V₁.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁)
      = sinj1 (V₀ := V₀') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₁.toElementMap x₁) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · have hXX : X = Y₀ := j1_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₁.rel_cod hf, rfl, ⟨Y₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j1 X, Or.inr ⟨X, x₁.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inl ⟨X, x₁.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩))⟩

end SumInjMap
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- `(f₀+f₁+f₂)(inj₂ x) = inj₂(f₂ x)`. -/
theorem sumMap3_sinj2 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₂ : V₂.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂)
      = sinj2 (V₀ := V₀') (V₁ := V₁') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₂.toElementMap x₂) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · have hXX : X = Z₀ := j2_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₂.rel_cod hf, rfl, ⟨Z₀, hx, hXX ▸ hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j2 X, Or.inr ⟨X, x₂.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inr ⟨X, x₂.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨X, Y', rfl, rfl, hf⟩))⟩

end SumInjMap
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example62C in
/-- The morphism action of `T`: `T(f) = I_𝟙 + f + f` (identity on the terminator, `f` on each
successor copy). Always strict (`isStrict_sumMap3`). -/
def tcMapHom {D E : StrictDomainObj.{w}} (f : (D ⟶ E)) :
    ((tcObj D) ⟶ (tcObj E)) :=
  ⟨sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1, isStrict_sumMap3 _ _ _⟩
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example62C in
/- concordance: source L4077 EXERCISE 6.17 algebras for sequence domains -/
/-- **Exercise 6.17 — the functor `T(X) = 𝟙 + X + X`** on the category of `∅`-free domains and strict
maps. On objects, `T(D) = 𝟙 + D + D` (Example 6.2's three-way sum); on maps, `T(f) = I_𝟙 + f + f`. -/
abbrev Tc : Endofunctor StrictDomainObj.{w} where
  obj := tcObj
  map := tcMapHom
  map_id D := Subtype.ext (by
    show sumMap3 (idMap unitSys) (idMap D.sys) (idMap D.sys) = idMap (tcObj D).sys
    exact sumMap3_id)
  map_comp {D E F} g f := Subtype.ext (by
    show sumMap3 (idMap unitSys) (g.1.comp f.1) (g.1.comp f.1)
      = (sumMap3 (idMap unitSys) g.1 g.1).comp (sumMap3 (idMap unitSys) f.1 f.1)
    have h := sumMap3_comp (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (h₀'' := Example62C.unitSys_nonempty) (h₁'' := F.nonempty) (h₂'' := F.nonempty)
      (idMap unitSys) g.1 g.1 (idMap unitSys) f.1 f.1
    rw [idMap_comp] at h
    exact h)
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem Tc_obj (D : StrictDomainObj.{w}) : Tc.obj D = tcObj D := rfl
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem Tc_map_val {D E : StrictDomainObj.{w}} (f : (D ⟶ E)) :
    (Tc.map f).1 = sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1 := rfl
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

open Example44 Example62C ExampleB in
/-- `C` (Example 4.4: finite-or-infinite binary sequences) as an object of the `∅`-free category. -/
abbrev Cobj : StrictDomainObj.{0} := ⟨Str, C, C_nonempty⟩
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

@[simp] theorem ccEquiv_apply (x : C.Element) : ccEquiv x = toCC x := rfl

end Example62C
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

/-- `(b·z).mem (bX) ↔ z.mem X`: the `b`-successor's filter restricted to the `b`-copy is `z`. -/
theorem consMap_mem_embBit {b : Bool} {z : C.Element} {X : Set Str} (hX : C.mem X) :
    ((consMap b).toElementMap z).mem (embBit b X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', _, _, hsub⟩
    rw [← embBit_eq_prepend] at hsub
    exact z.up_mem hzX' hX (embBit_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memC_embBit b hX, ?_⟩
    rw [← embBit_eq_prepend]

end Example62C
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

/-- `(b·z)` never meets the `(¬b)`-copy: `0z` avoids the `1`-copies and vice versa (used to discharge
the cross-tag cases in `toCC_consMap`). -/
theorem consMap_not_mem_embBit_ne {b c : Bool} (hbc : b ≠ c) {z : C.Element} {X : Set Str} :
    ¬ ((consMap b).toElementMap z).mem (embBit c X) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  obtain ⟨w, hw, heq⟩ := hsub ⟨a, rfl, ha⟩
  rw [List.cons.injEq] at hw; exact hbc hw.1

end Example62C
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

/-- `(b·z)` avoids the terminator `{Λ}` (since `bσ ≠ Λ`). -/
theorem consMap_not_mem_nil {b : Bool} {z : C.Element} :
    ¬ ((consMap b).toElementMap z).mem ({[]} : Set Str) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  have := hsub ⟨a, rfl, ha⟩
  rw [Set.mem_singleton_iff] at this; exact absurd this (by simp)

end Example62C
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The distinguished point `e = k(Λ)`: the image under `k` of the terminator (`𝟙`-injection). -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinj0 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty)
    (h₂ := B.carrier.nonempty) unitSys.bot)

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The `b`-th successor operation `f_b = k ∘ inj_b`: `f₀` via the `0`-copy (`inj₁`), `f₁` via the
`1`-copy (`inj₂`). -/
def descF (b : Bool) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (cond b
    (sinj2 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y)
    (sinj1 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y))

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descF_mono (b : Bool) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B b y ≤ descF B b y' := by
  cases b
  · exact B.str.1.toElementMap_mono (sinj1_mono h)
  · exact B.str.1.toElementMap_mono (sinj2_mono h)

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The recursion `φ(Λ)=z`, `φ(b·σ)=f_b(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Str → B.carrier.sys.Element
  | [] => z
  | b :: σ => descF B b (descVal z σ)

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Str) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => exact congrArg (descF B b) ih

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descMap_hcone {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descMap_hsing {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial
end

end DomainTheory.NeighbourhoodSystems
end

section
/- concordance: source L4075 EXERCISES — Lecture VI exercises -/
-- Exercise617/descMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The homomorphism `C → E`.** Built by `liftC` from the head-recursion: `φ(σ⊥) = f_{σ}(⊥)` and
`φ(σ) = f_{σ}(e)`, interpreting `b₀b₁… ↦ f_{b₀}(f_{b₁}(…))`. -/
def descMap : ApproximableMap C B.carrier.sys :=
  liftC B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

end Initial

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

@[simp] theorem descMap_strBot (σ : Str) :
    (descMap B).toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ :=
  liftC_strBot _ _ _ _ _ σ

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

@[simp] theorem descMap_strElem (σ : Str) :
    (descMap B).toElementMap (strElem σ) = descVal B (descE B) σ :=
  liftC_strElem _ _ _ _ _ σ

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem C_bot_eq_strBot_nil : C.bot = strBot [] := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show (C.mem Y ∧ C.master ⊆ Y) ↔ (C.mem Y ∧ cone [] ⊆ Y)
  rw [C_master, cone_nil]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem ccEquiv_comp_symm :
    (ofIso ccEquiv).comp (ofIso ccEquiv.symm) = idMap (sum3 unitSys C C Example62C.unitSys_nonempty
      Example62C.C_nonempty Example62C.C_nonempty) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem ccEquiv_symm_comp : (ofIso ccEquiv.symm).comp (ofIso ccEquiv) = idMap C := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, C_bot_eq_strBot_nil, descMap_strBot]
  rfl

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The bundled strict homomorphism `C → E`. -/
def descStrict : (Cobj ⟶ B.carrier) := ⟨descMap B, descMap_strict B⟩

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `T(g)` on `⊥` is `⊥`; precomposed with `k` it is `⊥` (both maps are strict). -/
theorem genKeyBot (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strBot [])))
      = B.carrier.sys.bot := by
  have hb : toCC (strBot []) = (sum3 unitSys C C Example62C.unitSys_nonempty Example62C.C_nonempty
      Example62C.C_nonempty).bot := by
    rw [← C_bot_eq_strBot_nil, ← Example62C.ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMap3 (h₀ := Example62C.unitSys_nonempty)
    (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (idMap unitSys) g g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial
end

section
/-- The map of an order-isomorphism is strict (an iso of domains preserves `⊥`). -/
theorem isStrict_ofIso {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (e : V₀.Element ≃o V₁.Element) : IsStrict (ofIso e) := by
  rw [isStrict_iff_apply_bot, toElementMap_ofIso]
  exact e.map_bot
end

section
open Example44 Example62C in
/-- **The `T`-algebra structure on `C`.** `(tcObj Cobj).sys = 𝟙 + C + C` (definitionally Example 6.2's
`CC`), and the structure map `i : 𝟙 + C + C → C` is the inverse of the domain-equation isomorphism
`ccEquiv` (Example 6.2), realised as an approximable map by `ofIso`; it is strict by `isStrict_ofIso`.
Concretely `i` sends the terminator to `Λ̂` and each `b`-copy of `x` to `b·x`. -/
abbrev cStr : ((Tc.obj Cobj) ⟶ Cobj) :=
  ⟨ofIso (by exact ccEquiv.symm), isStrict_ofIso _⟩
end

section
open Example44 Example62C in
/-- **`C` is a `T`-algebra**, `(C, i)` with `T(X) = 𝟙 + X + X`. -/
abbrev Calg : TAlgebra Tc := ⟨Cobj, cStr⟩
end

section
namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC ∘ (0·) = inj₁` and `toCC ∘ (1·) = inj₂`.** Prepending the bit `b` to `z` is, across the
isomorphism `C ≅ 𝟙+C+C`, the injection of `z` into the `b`-th `C`-summand. -/
theorem toCC_consMap (b : Bool) (z : C.Element) :
    toCC ((consMap b).toElementMap z)
      = cond b
          (sinj2 (V₀ := unitSys) (V₁ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z)
          (sinj1 (V₀ := unitSys) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  cases b
  · simp only [Bool.cond_false]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact Or.inr ⟨X, hX, rfl, (consMap_mem_embBit hX).mp hz⟩
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))
  · simp only [Bool.cond_true]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
      · exact Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mp hz⟩
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))

end Example62C
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The composite `inj₀∘(...)` of `T(g)` applied to a successor reduces to the operation `f_b`. The
single computational step behind both existence and uniqueness, for an *arbitrary* `g`. -/
theorem genKey (g : ApproximableMap C B.carrier.sys) (b : Bool) (w : C.Element) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap
      (toCC ((consMap b).toElementMap w)))
      = descF B b (g.toElementMap w) := by
  rw [toCC_consMap]
  cases b
  · simp only [Bool.cond_false]; rw [sumMap3_sinj1]; rfl
  · simp only [Bool.cond_true]; rw [sumMap3_sinj2]; rfl

end Initial
end

section
namespace Example62C

open Example44 ExampleB Example62

/-- **`toCC Λ̂ = inj₀`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElem_nil :
    toCC (strElem []) = sinj0 (V₁ := C) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
      (h₂ := C_nonempty) unitSys.bot := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.univ, rfl, rfl, unitSys.bot.master_mem⟩
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
  · rintro (rfl | ⟨X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · obtain rfl : X = Set.univ := hX
      exact Or.inr (Or.inl ⟨rfl, memC_singleton [], subset_rfl⟩)

end Example62C
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `T(g)` on the terminator is the terminator; precomposed with `k` it is `e`. -/
theorem genKey0 (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strElem [])))
      = descE B := by
  rw [toCC_strElem_nil, sumMap3_sinj0, toElementMap_idMap]
  rfl

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- `C`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty)
        (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty) (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strBot]
      have h := genKey B (descMap B) b (strBot σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strElem]
      have h := genKey B (descMap B) b (strElem σ)
      rw [descMap_strElem] at h
      exact h.symm

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The homomorphism square**, read off at the level of underlying approximable maps:
`desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B) (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **The descent homomorphism `(C, i) → (E, k)`** as a `T`-algebra homomorphism. -/
def descAlgHom : AlgHom Calg B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** This is *both* the existence
witness (`descMap` satisfies it) and the uniqueness driver. -/
theorem rec_determines (g : ApproximableMap C B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKeyBot B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strBot]
      have h := genKey B g b (strBot σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElem σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKey0 B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strElem]
      have h := genKey B g b (strElem σ)
      rw [ih] at h
      exact h
  apply map_ext_C
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

end Initial
end

section
section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- **Uniqueness.** Any `T`-algebra homomorphism out of `(C, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom Calg B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
          (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
          (h₂' := B.carrier.nonempty) (idMap unitSys) hom.1 hom.1) :=
      congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial
end

section
/-- **Exercise 6.17 (existence half) — `(C, i)` is an initial `T`-algebra for `T(X) = 𝟙 + X + X`.**
The descent map `φ : C → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(b·x) = f_b(φ x)`
(`f_b = k ∘ inj_b`), built choice-free via `liftC`; it is the unique `T`-algebra homomorphism, so `C`
is determined (up to iso, Proposition 6.6) as the initial algebra of `X ↦ 𝟙 + X + X`. -/
def CisInitial : IsInitial Calg where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h
end

section
namespace Example62C

open Example44 ExampleB Example62

end Example62C
end

section
set_option linter.unusedVariables false

theorem example_617 : ∀
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc)
  (h' :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B)
    h' (DomainTheory.NeighbourhoodSystems.descAlgHom B) :=
  DomainTheory.NeighbourhoodSystems.descAlgHom_uniq
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
variable {A : Type} [DecidableEq A]

/-- The token type `A*` of finite `A`-strings. -/
abbrev Strn (A : Type) := List A
end

section
variable {A : Type} [DecidableEq A]

/-- The cone `σA*`: all extensions of `σ`. -/
def coneN (σ : Strn A) : Set (Strn A) := {w | σ <+: w}
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

@[simp] theorem mem_coneN {σ w : Strn A} : w ∈ coneN σ ↔ σ <+: w := Iff.rfl
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem coneN_nil : coneN ([] : Strn A) = Set.univ := by ext w; simp [coneN]
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem coneN_subset_coneN {σ τ : Strn A} : coneN σ ⊆ coneN τ ↔ τ <+: σ := by
  constructor
  · intro h; exact h (show σ ∈ coneN σ from List.prefix_rfl)
  · intro hτσ w hw; exact hτσ.trans hw
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem coneN_injective {σ τ : Strn A} (h : coneN σ = coneN τ) : σ = τ := by
  have h1 : τ <+: σ := coneN_subset_coneN.mp (le_of_eq h)
  have h2 : σ <+: τ := coneN_subset_coneN.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)
end

section
variable {A : Type} [DecidableEq A]

theorem coneN_trichotomy (σ τ : Strn A) :
    coneN σ ⊆ coneN τ ∨ coneN τ ⊆ coneN σ ∨ coneN σ ∩ coneN τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (coneN_subset_coneN.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (coneN_subset_coneN.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_coneN, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))
end

section
variable {A : Type} [DecidableEq A]

/-- Membership in `Cₐ`: a cone `σA*` or a singleton `{σ}`. -/
def memCn (X : Set (Strn A)) : Prop := (∃ σ, X = coneN σ) ∨ (∃ σ, X = {σ})
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem memCn_coneN (σ : Strn A) : memCn (coneN σ) := Or.inl ⟨σ, rfl⟩
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem memCn_singleton (σ : Strn A) : memCn ({σ} : Set (Strn A)) := Or.inr ⟨σ, rfl⟩
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem singleton_subset_coneN {σ τ : Strn A} : ({τ} : Set (Strn A)) ⊆ coneN σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_coneN]
end

section
variable {A : Type} [DecidableEq A]

theorem singleton_coneN_nd (σ τ : Strn A) :
    ({τ} : Set (Strn A)) ⊆ coneN σ ∨ coneN σ ⊆ {τ} ∨ ({τ} : Set (Strn A)) ∩ coneN σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_coneN.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_coneN, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ
end

section
variable {A : Type} [DecidableEq A]

theorem nestedOrDisjointN : NestedOrDisjoint (memCn (A := A)) := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact coneN_trichotomy σ τ
  · rcases singleton_coneN_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_coneN_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2
end

section
variable {A : Type} [DecidableEq A]

/-- **The generic domain `Cₐ`** of finite-or-infinite `A`-sequences. -/
abbrev Cn (A : Type) [DecidableEq A] : NeighborhoodSystem (Strn A) :=
  NeighborhoodSystem.ofNestedOrDisjoint memCn Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], coneN_nil.symm⟩) nestedOrDisjointN
    (fun _ => Set.subset_univ _)
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem Cn_mem {X : Set (Strn A)} : (Cn A).mem X ↔ memCn X := Iff.rfl
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem Cn_master : (Cn A).master = (Set.univ : Set (Strn A)) := rfl
end

section
variable {A : Type} [DecidableEq A]

/-- `Cₐ` is `∅`-free: every neighbourhood is non-empty (cones and singletons are inhabited). -/
theorem Cn_nonempty : ∀ X, (Cn A).mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩
end

section
variable {A : Type} [DecidableEq A]

/-- `σX = {στ ∣ τ ∈ X}`. -/
def prependN (σ : Strn A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

@[simp] theorem mem_prependN {σ : Strn A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ prependN σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem prependN_coneN (σ ρ : Strn A) : prependN σ (coneN ρ) = coneN (σ ++ ρ) := by
  ext w
  simp only [mem_prependN, mem_coneN]
  constructor
  · rintro ⟨τ, hτ, rfl⟩; exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem prependN_mono (σ : Strn A) {X X' : Set (Strn A)} (h : X' ⊆ X) :
    prependN σ X' ⊆ prependN σ X := by
  rintro w ⟨τ, hτ, rfl⟩; exact ⟨τ, h hτ, rfl⟩
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem prependN_singleton (σ τ : Strn A) : prependN σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prependN, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩
end

section
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem memCn_prependN (σ : Strn A) {X : Set (Strn A)} (hX : memCn X) : memCn (prependN σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prependN_coneN σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prependN_singleton σ ρ⟩
end

section
variable {A : Type} [DecidableEq A]

/-- **The successor `x ↦ a·x`** prepending the letter `a`: `X (a·x) Y ↔ aX ⊆ Y`. -/
def consMapN (a : A) : ApproximableMap (Cn A) (Cn A) where
  rel X Y := memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Or.inl ⟨[], coneN_nil.symm⟩, Or.inl ⟨[], coneN_nil.symm⟩,
    fun _ _ => trivial⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    have hsubInter : prependN [a] X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hZ : memCn (prependN [a] X) := memCn_prependN [a] hX
    exact ⟨hX, (Cn A).inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prependN_mono [a] hX'X).trans (hXY.trans hYY')⟩
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem consMapN_rel {a : A} {X Y : Set (Strn A)} :
    (consMapN a).rel X Y ↔ memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y := Iff.rfl
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- Tokens of the indexed sum `𝟙 + Σ_a β`. -/
abbrev SigTok (A : Type) (β : Type v) := Option (Unit ⊕ (A × β))

end SumSig
end

section
variable {A : Type} [DecidableEq A]

/-- The partial element `σ⊥ = ↑σA*`. -/
def strBotN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_coneN σ))
end

section
variable {A : Type} [DecidableEq A]

theorem consMapN_strBot (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strBotN σ) = strBotN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXcone⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc coneN (a :: σ) = prependN [a] (coneN σ) := by rw [prependN_coneN]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXcone
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, memCn_coneN σ, hY, ?_⟩
    rw [show prependN [a] (coneN σ) = coneN (a :: σ) by rw [prependN_coneN]; rfl]
    exact hsub
end

section
variable {A : Type} [DecidableEq A]

/-- The total element `σ = ↑{σ}`. -/
def strElemN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_singleton σ))
end

section
variable {A : Type} [DecidableEq A]

theorem consMapN_strElem (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strElemN σ) = strElemN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXsing⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc ({a :: σ} : Set (Strn A)) = prependN [a] {σ} := by rw [prependN_singleton]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXsing
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, memCn_singleton σ, hY, ?_⟩
    rw [show prependN [a] ({σ} : Set (Strn A)) = {a :: σ} by rw [prependN_singleton]; rfl]
    exact hsub
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- The token `t` in the `a`-indexed copy. -/
def tc (a : A) (t : β) : SigTok A β := some (Sum.inr (a, t))

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- The `a`-indexed tagged copy `aX`. -/
def jc (a : A) (X : Set β) : Set (SigTok A β) := {w | ∃ t, w = tc a t ∧ t ∈ X}

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem tc_injective {a a' : A} {t t' : β} (h : (tc a t : SigTok A β) = tc a' t') :
    a = a' ∧ t = t' := by
  simp only [tc, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem tc_mem_jc {a : A} {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∈ jc a X ↔ t ∈ X := by
  constructor
  · rintro ⟨t', heq, ht'⟩; obtain ⟨-, rfl⟩ := tc_injective heq; exact ht'
  · intro ht; exact ⟨t, rfl, ht⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- The lone `𝟙`-token. -/
def tu : SigTok A β := some (Sum.inl ())

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- The `𝟙`-copy neighbourhood (the image of `univ : Set Unit`). -/
def jU : Set (SigTok A β) := {tu}

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem mem_jU {w : SigTok A β} : w ∈ (jU : Set (SigTok A β)) ↔ w = tu := Iff.rfl

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem none_not_mem_jU : (none : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu]

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem none_not_mem_jc {a : A} {X : Set β} : (none : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tc])

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem tu_not_mem_jc {a : A} {X : Set β} : (tu : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tu, tc])

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

@[simp] theorem tc_not_mem_jU {a : A} {t : β} : (tc a t : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu, tc]

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jU_inter_jc (a : A) (X : Set β) : (jU ∩ jc a X : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_jU, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl; exact tu_not_mem_jc

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jU_nonempty : (jU : Set (SigTok A β)).Nonempty := ⟨tu, rfl⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_inter_jc_ne {a a' : A} (h : a ≠ a') (X X' : Set β) :
    (jc a X ∩ jc a' X' : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl, -⟩ ⟨t', heq, -⟩
  exact h (tc_injective heq).1

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_inter_jc_same (a : A) (X X' : Set β) :
    (jc a X ∩ jc a X' : Set (SigTok A β)) = jc a (X ∩ X') := by
  ext w
  constructor
  · rintro ⟨⟨t, rfl, ht⟩, ⟨t', heq, ht'⟩⟩
    obtain ⟨-, rfl⟩ := tc_injective heq; exact ⟨t, rfl, ht, ht'⟩
  · rintro ⟨t, rfl, ht, ht'⟩; exact ⟨⟨t, rfl, ht⟩, ⟨t, rfl, ht'⟩⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_nonempty {a : A} {X : Set β} (hX : X.Nonempty) : (jc a X : Set (SigTok A β)).Nonempty := by
  obtain ⟨t, ht⟩ := hX; exact ⟨tc a t, t, rfl, ht⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_subset_jc {a : A} {X X' : Set β} :
    (jc a X : Set (SigTok A β)) ⊆ jc a X' ↔ X ⊆ X' := by
  constructor
  · intro h t ht; exact tc_mem_jc.mp (h (tc_mem_jc.mpr ht))
  · rintro h w ⟨t, rfl, ht⟩; exact tc_mem_jc.mpr (h ht)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_injective {a : A} {X X' : Set β} (h : (jc a X : Set (SigTok A β)) = jc a X') : X = X' :=
  Set.Subset.antisymm (jc_subset_jc.mp h.subset) (jc_subset_jc.mp h.symm.subset)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in
/-- Tagged copies determine both index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`,
`X=X'`. -/
theorem jc_eq_jc {a a' : A} {X X' : Set β} (hXne : X.Nonempty)
    (heq : (jc a X : Set (SigTok A β)) = jc a' X') : a = a' ∧ X = X' := by
  obtain ⟨t, ht⟩ := hXne
  obtain ⟨t', he, -⟩ := heq ▸ (tc_mem_jc.mpr ht)
  obtain ⟨rfl, -⟩ := tc_injective he
  exact ⟨rfl, jc_injective heq⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

/-- The master neighbourhood `{Λ} ∪ {tu} ∪ ⋃_a aΔ`. -/
def masterSig : Set (SigTok A β) :=
  {w | w = none ∨ w = tu ∨ ∃ a t, t ∈ V.master ∧ w = tc a t}

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

@[simp] theorem none_mem_masterSig : (none : SigTok A β) ∈ masterSig V := Or.inl rfl

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem tc_mem_jc_ne {a a' : A} (h : a ≠ a') {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∉ jc a' X := by
  rintro ⟨t', heq, -⟩; exact h (tc_injective heq).1

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

@[simp] theorem tu_mem_masterSig : (tu : SigTok A β) ∈ masterSig V := Or.inr (Or.inl rfl)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

theorem eq_masterSig_of_subset {W : Set (SigTok A β)}
    (hsub : masterSig V ⊆ W) (hsub' : W ⊆ masterSig V) : W = masterSig V :=
  Set.Subset.antisymm hsub' hsub

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

theorem jU_subset_masterSig : (jU : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w rfl; exact tu_mem_masterSig

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

theorem jc_subset_masterSig {a : A} {X : Set β} (hX : V.mem X) :
    (jc a X : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w ⟨t, rfl, ht⟩; exact Or.inr (Or.inr ⟨a, t, V.sub_master hX ht, rfl⟩)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

theorem masterSig_inter_jU : (masterSig V ∩ jU : Set (SigTok A β)) = jU :=
  Set.inter_eq_right.mpr jU_subset_masterSig

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

omit [DecidableEq A] in

theorem masterSig_inter_jc {a : A} {X : Set β} (hX : V.mem X) :
    (masterSig V ∩ jc a X : Set (SigTok A β)) = jc a X :=
  Set.inter_eq_right.mpr (jc_subset_masterSig hX)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

/-- **The `A`-indexed separated sum `𝟙 + Σ_a V`** over `{Λ} ∪ {tu} ∪ ⋃_a aΔ`, under the standing
assumption that no neighbourhood of `V` is empty. The alphabet-generic analogue of `sum3 unitSys V V`
(Example 6.2). -/
def sumSig (A : Type) [DecidableEq A] (V : NeighborhoodSystem β)
    (h : ∀ X, V.mem X → X.Nonempty) :
    NeighborhoodSystem (SigTok A β) where
  mem W := W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X
  master := masterSig V
  master_nonempty := ⟨none, none_mem_masterSig⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
    · exact subset_rfl
    · exact jU_subset_masterSig
    · exact jc_subset_masterSig hX
  inter_mem := by
    have hne : ∀ W, (W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X) →
        (W : Set (SigTok A β)).Nonempty := by
      rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
      · exact ⟨none, none_mem_masterSig⟩
      · exact jU_nonempty
      · exact jc_nonempty (h X hX)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [masterSig_inter_jc hX']; exact Or.inr (Or.inr ⟨a', X', hX', rfl⟩)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [Set.inter_self]; exact Or.inr (Or.inl rfl)
      · rw [jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jc hX]; exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
      · rw [Set.inter_comm, jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · by_cases haa : a = a'
        · subst haa
          rw [jc_inter_jc_same] at hZsub ⊢
          rcases hZ with rfl | rfl | ⟨a₂, Z₂, hZ₂, rfl⟩
          · exact absurd (hZsub none_mem_masterSig) (by simp)
          · exact absurd (hZsub (show tu ∈ jU from rfl)) tu_not_mem_jc
          · by_cases ha₂ : a = a₂
            · subst ha₂
              exact Or.inr (Or.inr ⟨a, X ∩ X', V.inter_mem hX hX' hZ₂ (jc_subset_jc.mp hZsub), rfl⟩)
            · obtain ⟨t, ht⟩ := h Z₂ hZ₂
              exact absurd (hZsub (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm ha₂))
        · rw [jc_inter_jc_ne haa] at hZsub ⊢
          obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

@[simp] theorem sumSig_master {h : ∀ X, V.mem X → X.Nonempty} :
    (sumSig A V h).master = masterSig V := rfl

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- A `sumSig`-neighbourhood contained in the `𝟙`-copy `jU` is `jU`. -/
theorem mem_subset_jU_inv {W : Set (SigTok A β)}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jU) : W = jU := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jU
  · rfl
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- A `sumSig`-neighbourhood contained in an `a`-copy `aX` is itself an `a`-copy. -/
theorem mem_subset_jc_inv {W : Set (SigTok A β)} {a : A} {X : Set β}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jc a X) : ∃ X₂, V.mem X₂ ∧ W = jc a X₂ := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jc
  · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
    obtain ⟨rfl, -⟩ := tc_injective heq
    exact ⟨X₂, hX₂, rfl⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- The `a`-th copy injection `V ↪ 𝟙+Σ_a V`: send `x∈|V|` to the sum element whose proper
neighbourhoods are the `a`-copies `aX` with `X∈x`. -/
def sinjC (a : A) (x : V.Element) : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ ∃ X, V.mem X ∧ W = jc a X ∧ x.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [masterSig_inter_jc hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x.sub (x.inter_mem hx hx'), jc_inter_jc_same a X X', x.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective heq
        exact Or.inr ⟨X', hX', rfl, x.up_mem hx hX' (jc_subset_jc.mp hsub)⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- The basepoint/`𝟙`-injection: the image of the unique point of `𝟙`. Its proper neighbourhood is
the `𝟙`-copy `jU`. -/
def sinjU : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ W = jU
  sub := by
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | rfl) (rfl | rfl)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (by rw [masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_comm, masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_self])
  up_mem := by
    rintro W W' (rfl | rfl) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

@[simp] theorem sinjU_mem_jU : (sinjU (h := h)).mem (jU : Set (SigTok A β)) := Or.inr rfl

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

@[simp] theorem sinjC_mem_jc {a : A} {x : V.Element} {X : Set β} (hX : V.mem X) :
    (sinjC (h := h) a x).mem (jc a X) ↔ x.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · rw [jc_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

theorem sinjC_mono {a : A} {x x' : V.Element} (hxle : x ≤ x') :
    sinjC (h := h) a x ≤ sinjC a x' := by
  rintro W (rfl | ⟨X, hX, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, hX, rfl, hxle X hm⟩

end SumSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **The indexed sum map `Σf = I_𝟙 + Σ_a f`** acting as the identity on the `𝟙`-summand and as `f`
on each `a`-copy. The generic analogue of `sumMap3 (idMap unitSys) f f`. -/
def sumMapSig (f : ApproximableMap V₀ V₁) :
    ApproximableMap (sumSig A V₀ h₀) (sumSig A V₁ h₁) where
  rel W W' := (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
    (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
      ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y')
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨(sumSig A V₀ h₀).master_mem, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (SigTok A β₁),
        (W'' = masterSig V₁ ∨ (W = jU ∧ W'' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W'' = jc a Y' ∧ f.rel X Y') → (sumSig A V₁ h₁).mem W'' := by
      rintro W'' (rfl | ⟨-, rfl⟩ | ⟨a, X, Y', -, rfl, hf⟩)
      · exact (sumSig A V₁ h₁).master_mem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩)
    have key : (W'₁ ∩ W'₂ = masterSig V₁ ∨ (W = jU ∧ W'₁ ∩ W'₂ = jU) ∨
        ∃ a X Y', W = jc a X ∧ W'₁ ∩ W'₂ = jc a Y' ∧ f.rel X Y') := by
      rcases hd₁ with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Y'₁, hWX, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ masterSig V₁ from
          (sumSig A V₁ h₁).sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hWX, rfl, hf⟩
        · rw [Set.inter_eq_left.mpr jU_subset_masterSig]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · rw [Set.inter_self]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf)
          exact absurd ((hWX.symm.trans hWU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · rcases hd₂ with rfl | ⟨hWU2, rfl⟩ | ⟨a', X', Y'₂, hWX', rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (jc_subset_masterSig (f.rel_cod hf₁))]
          exact Or.inr (Or.inr ⟨a, X, Y'₁, hWX, rfl, hf₁⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf₁)
          exact absurd ((hWX.symm.trans hWU2) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
        · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X (f.rel_dom hf₁)) (hWX.symm.trans hWX')
          rw [jc_inter_jc_same]
          exact Or.inr (Or.inr ⟨a, X, Y'₁ ∩ Y'₂, hWX, rfl, f.inter_right hf₁ hf₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_masterSig_of_subset hW'W'₂ ((sumSig A V₁ h₁).sub_master hW'₂mem))
    · have hW₂jU : W₂ = jU := mem_subset_jU_inv hW₂mem hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hW₂jU, rfl⟩)
      · exact absurd (hW'W'₂ (show tu ∈ jU from rfl)) tu_not_mem_jc
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_jc_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := jc_subset_jc.mp hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        exact absurd (hW'W'₂ (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        obtain ⟨t', he, -⟩ := hW'W'₂ (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X₂, Y'₂, rfl, rfl,
          f.mono hf hX₂X (jc_subset_jc.mp hW'W'₂) hX₂ hY'₂⟩)

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The sum map is strict: it sends `⊥ = master` only to `master`. -/
theorem isStrict_sumMapSig (f : ApproximableMap V₀ V₁) :
    IsStrict (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  rintro W' ⟨-, -, hd⟩
  rcases hd with rfl | ⟨hWU, -⟩ | ⟨a, X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWU ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jU
  · exact absurd (hWX ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jc

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

@[simp] theorem sumMapSig_rel {f : ApproximableMap V₀ V₁} {W W'} :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).rel W W' ↔
      (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
        (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y') := Iff.rfl

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **Functoriality (composition): `Σ(g∘f) = Σg ∘ Σf`.** -/
theorem sumMapSig_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    sumMapSig (A := A) (h₀ := h₀) (h₁ := h₂) (g.comp f)
      = (sumMapSig (A := A) (h₀ := h₁) (h₁ := h₂) g).comp
          (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨masterSig V₁, ⟨hW, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩,
        (sumSig A V₁ h₁).master_mem, hW'', Or.inl rfl⟩
    · exact ⟨jU, ⟨hW, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨hWU, rfl⟩)⟩,
        Or.inr (Or.inl rfl), hW'', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨jc a Y', ⟨hW, Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩),
        Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), hW'',
        Or.inr (Or.inr ⟨a, Y', Z'', rfl, rfl, hg⟩)⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, -, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨hW'U, rfl⟩ | ⟨a, Y', Z'', hW'Y', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨hWU, -⟩ | ⟨a, X, Y'₀, -, hW'eq, hf⟩
      · exact absurd ((hW'U.symm) ▸ none_mem_masterSig) none_not_mem_jU
      · exact Or.inr (Or.inl ⟨hWU, rfl⟩)
      · obtain ⟨t, ht⟩ := h₁ Y'₀ (f.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'U) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hdf with rfl | ⟨-, hW'U⟩ | ⟨a', X, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨t, ht⟩ := h₁ Y' (g.rel_dom hg)
        exact absurd ((hW'U.symm.trans hW'Y') ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₁ Y'₀ (f.rel_cod hf)) (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr ⟨a', X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **Functoriality (identities): `Σ(I) = I`.** -/
theorem sumMapSig_id :
    sumMapSig (A := A) (V₀ := V₀) (V₁ := V₀) (h₀ := h₀) (h₁ := h₀) (idMap V₀)
      = idMap (sumSig A V₀ h₀) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, -, -, hXY⟩
    · exact (sumSig A V₀ h₀).sub_master hW
    · exact subset_rfl
    · exact jc_subset_jc.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V₀ h₀).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₀ X hX; exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X, X', rfl, rfl, hX, hX', jc_subset_jc.mp hsub⟩)

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- `Σf` on the `a`-copy injection: `(Σf)(inj_a x) = inj_a (f x)`. -/
theorem sumMapSig_sinjC (f : ApproximableMap V₀ V₁) (a : A) (x : V₀.Element) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjC (h := h₀) a x)
      = sinjC (h := h₁) a (f.toElementMap x) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨hUjU, rfl⟩ | ⟨a', X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUjU) ▸ none_mem_masterSig) none_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X₀ hX₀
        exact absurd ((hUeq.symm.trans hUjU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X₀ hX₀) (hUeq.symm.trans hUj)
        exact Or.inr ⟨Y', f.rel_cod hf, rfl, ⟨X₀, hx, hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨jc a X, Or.inr ⟨X, x.sub hx, rfl, hx⟩, Or.inr (Or.inr ⟨a, X, x.sub hx, rfl⟩),
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- `Σf` fixes the basepoint injection. -/
theorem sumMapSig_sinjU (f : ApproximableMap V₀ V₁) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjU (h := h₀))
      = sinjU (h := h₁) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hU with hUm | rfl
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · exact absurd (hUj ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · rintro (rfl | rfl)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · exact ⟨jU, Or.inr rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

end SumMapSig
end

section
variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

theorem sumSig_nonempty {h : ∀ X, V.mem X → X.Nonempty} :
    ∀ W, (sumSig A V h).mem W → W.Nonempty := by
  rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
  · exact ⟨none, none_mem_masterSig⟩
  · exact jU_nonempty
  · exact jc_nonempty (h X hX)

end SumSig
end

section
variable {A : Type} [DecidableEq A]

/-- `Tsig` on objects: `Tsig(D) = 𝟙 + Σ_a D`, again `∅`-free (`sumSig_nonempty`). -/
abbrev tsigObj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) : StrictDomainObj.{0} where
  carrier := SigTok A D.carrier
  sys := sumSig A D.sys D.nonempty
  nonempty := sumSig_nonempty
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem tsigObj_sys (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (tsigObj A D).sys = sumSig A D.sys D.nonempty := rfl
end

section
variable {A : Type} [DecidableEq A]

/-- `Tsig` on maps: `Tsig(f) = I_𝟙 + Σ_a f`, strict by `isStrict_sumMapSig`. -/
def tsigMapHom (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}} (f : (D ⟶ E)) :
    ((tsigObj A D) ⟶ (tsigObj A E)) :=
  ⟨sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1, isStrict_sumMapSig _⟩
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem tsigMapHom_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : (D ⟶ E)) :
    (tsigMapHom A f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl
end

section
variable {A : Type} [DecidableEq A]

/-- **The functor `Tsig(X) = 𝟙 + Σ_{a:A} X`** on the category of `∅`-free domains and strict maps. -/
abbrev Tsig (A : Type) [DecidableEq A] : Endofunctor StrictDomainObj.{0} where
  obj := tsigObj A
  map := tsigMapHom A
  map_id _ := Subtype.ext sumMapSig_id
  map_comp {_ _ _} g f := Subtype.ext (sumMapSig_comp g.1 f.1)
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem Tsig_obj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (Tsig A).obj D = tsigObj A D := rfl
end

section
variable {A : Type} [DecidableEq A]

@[simp] theorem Tsig_map_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : (D ⟶ E)) :
    ((Tsig A).map f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `aX = {a :: w' ∣ w' ∈ X}`: the `a`-prefixed copy of a neighbourhood. -/
def embA (a : A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ w', w = a :: w' ∧ w' ∈ X}

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

@[simp] theorem mem_embA {a : A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ embA a X ↔ ∃ w', w = a :: w' ∧ w' ∈ X := Iff.rfl

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- The right-hand side of the domain equation: the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/
abbrev CCn (A : Type) [DecidableEq A] : NeighborhoodSystem (SigTok A (Strn A)) :=
  sumSig A (Cn A) Cn_nonempty

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_eq_prependN (a : A) (X : Set (Strn A)) : embA a X = prependN [a] X := by
  ext w
  simp only [mem_embA, mem_prependN]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨t, hX, rfl⟩; exact ⟨t, rfl, hX⟩

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_coneN (a : A) (σ : Strn A) : embA a (coneN σ) = coneN (a :: σ) := by
  rw [embA_eq_prependN, prependN_coneN]; rfl

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_inter (a : A) (X X' : Set (Strn A)) : embA a X ∩ embA a X' = embA a (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩; exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_inter_ne {a a' : A} (h : a ≠ a') (X Y : Set (Strn A)) :
    embA a X ∩ embA a' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq; exact h heq.1

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_singleton (a : A) (σ : Strn A) : embA a ({σ} : Set (Strn A)) = {a :: σ} := by
  rw [embA_eq_prependN, prependN_singleton]; rfl

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_subset {a : A} {X X' : Set (Strn A)} : embA a X ⊆ embA a X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact hX'
  · rintro h w ⟨w', rfl, hX⟩; exact ⟨w', rfl, h hX⟩

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_injective {a : A} {X X' : Set (Strn A)} (h : embA a X = embA a X') : X = X' :=
  Set.Subset.antisymm (embA_subset.mp h.subset) (embA_subset.mp h.symm.subset)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in
/-- **The shape of a `Cₐ`-neighbourhood.** Every neighbourhood is the master `Σ*`, the terminator
`{Λ}`, or an `a`-copy `aX` with `X ∈ Cₐ`. -/
theorem memCn_cases {W : Set (Strn A)} (hW : memCn W) :
    W = Set.univ ∨ W = ({[]} : Set (Strn A)) ∨ ∃ a X, memCn X ∧ W = embA a X := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl coneN_nil
    | cons a σ' => exact Or.inr (Or.inr ⟨a, coneN σ', memCn_coneN σ', (embA_coneN a σ').symm⟩)
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons a σ' => exact Or.inr (Or.inr ⟨a, {σ'}, memCn_singleton σ', (embA_singleton a σ').symm⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

omit [DecidableEq A] in

theorem memCn_embA (a : A) {X : Set (Strn A)} (hX : memCn X) : memCn (embA a X) := by
  rw [embA_eq_prependN]; exact memCn_prependN [a] hX

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem memCn_embA_inv {a : A} {W : Set (Strn A)} (h : memCn (embA a W)) : memCn W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embA a W := hσ ▸ (show σ ∈ coneN σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_coneN] at hσ; rw [embA_injective hσ]; exact memCn_coneN w'
  · have hmem : σ ∈ embA a W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set (Strn A)))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_singleton] at hσ; rw [embA_injective hσ]; exact memCn_singleton w'

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem nil_not_mem_embA {a : A} {X : Set (Strn A)} : ([] : Strn A) ∉ embA a X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem embA_ne_univ (a : A) (X : Set (Strn A)) : embA a X ≠ Set.univ := by
  intro h; exact nil_not_mem_embA (X := X) (a := a) (by rw [h]; trivial)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem singleton_nil_inter_embA (a : A) (X : Set (Strn A)) :
    (({[]} : Set (Strn A)) ∩ embA a X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embA, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩; exact absurd heq (by simp)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in

theorem singleton_nil_ne_embA (a : A) (X : Set (Strn A)) :
    ({[]} : Set (Strn A)) ≠ embA a X := by
  intro h
  exact nil_not_mem_embA (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Strn A) ∈ ({[]} : Set (Strn A))))

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] in

theorem singleton_nil_ne_univ : ({[]} : Set (Strn A)) ≠ Set.univ := by
  intro h
  have hmem : ([default] : Strn A) ∈ ({[]} : Set (Strn A)) := by rw [h]; trivial
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem sumSig_mem_jc_inv {a : A} {X : Set (Strn A)} (h : (CCn A).mem (jc a X)) :
    (Cn A).mem X := by
  rcases h with h0 | hU | ⟨a', X', hX', heq⟩
  · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
  · have : (tu : SigTok A (Strn A)) ∈ jc a X := by rw [hU]; rfl
    exact absurd this tu_not_mem_jc
  · by_cases haa : a = a'
    · subst haa; rw [jc_injective heq]; exact hX'
    · obtain ⟨t, ht⟩ := Cn_nonempty X' hX'
      exact absurd (heq.symm ▸ (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm haa))

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **Forward half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** Records, for each branch, whether `x` finishes at `Λ`
(the `𝟙`-summand) or reaches the `a`-copy `aX` (the `a`-th summand). -/
def toCC (x : (Cn A).Element) : (CCn A).Element where
  mem W := W = masterSig (Cn A)
    ∨ (W = jU ∧ x.mem ({[]} : Set (Strn A)))
    ∨ (∃ a X, (Cn A).mem X ∧ W = jc a X ∧ x.mem (embA a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨a', X', hX', rfl, hzF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [masterSig_inter_jU], hzU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [masterSig_inter_jc hX'], hzF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, masterSig_inter_jU], hzU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hzU⟩)
    · exfalso
      have hx := x.inter_mem hzU hzF'; rw [singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hzF⟩)
    · exfalso
      have hx := x.inter_mem hzF hzU'; rw [Set.inter_comm, singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hx := x.inter_mem hzF hzF'; rw [embA_inter] at hx
        exact Or.inr (Or.inr ⟨a, X ∩ X', memCn_embA_inv (x.sub hx), jc_inter_jc_same a X X', hx⟩)
      · exfalso
        have hx := x.inter_mem hzF hzF'; rw [embA_inter_ne haa] at hx
        obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((CCn A).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X', hX', rfl,
          x.up_mem hzF (memCn_embA a hX') (embA_subset.mpr (jc_subset_jc.mp hsub))⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

@[simp] theorem toCC_mem_jU {x : (Cn A).Element} :
    (toCC x).mem (jU : Set (SigTok A (Strn A))) ↔ x.mem ({[]} : Set (Strn A)) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨a', X', hX', heq, hz⟩)
    · exact absurd (h0.symm ▸ none_mem_masterSig) none_not_mem_jU
    · exact hz
    · exact absurd (heq ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

@[simp] theorem toCC_mem_jc {x : (Cn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (toCC x).mem (jc a X) ↔ x.mem (embA a X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨a', X', hX', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · obtain ⟨t, ht⟩ := Cn_nonempty X hX
      exact absurd (heq ▸ (tc_mem_jc.mpr ht)) tc_not_mem_jU
    · obtain ⟨rfl, rfl⟩ := jc_eq_jc (Cn_nonempty X hX) heqj
      exact hz
  · intro hz; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hz⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [DecidableEq A] [Inhabited A] in
/-- Prefixed copies determine index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`, `X=X'`. -/
theorem embA_eq_embA {a a' : A} {X X' : Set (Strn A)} (hXne : X.Nonempty)
    (h : embA a X = embA a' X') : a = a' ∧ X = X' := by
  obtain ⟨w', hw'⟩ := hXne
  have hmem : (a :: w') ∈ embA a X := ⟨w', rfl, hw'⟩
  rw [h] at hmem
  obtain ⟨u, he, -⟩ := hmem
  rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
  exact ⟨rfl, embA_injective h⟩

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **Inverse half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
def fromCC (s : (CCn A).Element) : (Cn A).Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set (Strn A)) ∧ s.mem jU)
    ∨ (∃ a X, (Cn A).mem X ∧ W = embA a X ∧ s.mem (jc a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl ⟨[], coneN_nil.symm⟩
    · exact memCn_singleton []
    · exact memCn_embA a hX
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨a', X', hX', rfl, hsF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [Set.univ_inter], hsF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_univ], hsF⟩)
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_same] at hs
        exact Or.inr (Or.inr ⟨a, X ∩ X', sumSig_mem_jc_inv (s.sub hs), embA_inter a X X', hs⟩)
      · exfalso
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_ne haa] at hs
        obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        have hm := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
        refine Or.inr (Or.inr ⟨a, X', hX', rfl, ?_⟩)
        exact s.up_mem hsF (Or.inr (Or.inr ⟨a, X', hX', rfl⟩))
          (jc_subset_jc.mpr (embA_subset.mp hsub))

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

@[simp] theorem fromCC_mem_nil {s : (CCn A).Element} :
    (fromCC s).mem ({[]} : Set (Strn A)) ↔ s.mem (jU : Set (SigTok A (Strn A))) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨a', X', hX', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embA a' X')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

@[simp] theorem fromCC_mem_embA {s : (CCn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (fromCC s).mem (embA a X) ↔ s.mem (jc a X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨a', X', hX', heqj, hs⟩)
    · exact absurd h0 (embA_ne_univ a X)
    · exact absurd heq.symm (singleton_nil_ne_embA a X)
    · obtain ⟨rfl, rfl⟩ := embA_eq_embA (Cn_nonempty X hX) heqj
      exact hs
  · intro hs; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hs⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem fromCC_toCC (x : (Cn A).Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_jU.mp hs
    · exact (toCC_mem_jc hX).mp hs
  · intro hW
    rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_jU.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (toCC_mem_jc hX).mpr hW⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

theorem toCC_fromCC (s : (CCn A).Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embA hX).mp hs
  · intro hW
    rcases s.sub hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (fromCC_mem_embA hX).mpr hW⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **The isomorphism `|Cₐ| ≃o |𝟙 + Σ_a Cₐ|`.** -/
def ccEquiv : (Cn A).Element ≃o (CCn A).Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro hle W hW
      rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_jU.mp (hle _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_jc hX).mp (hle _ (Or.inr (Or.inr ⟨a, X, hX, rfl, hW⟩)))
    · intro hle W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hle _ hz⟩)
      · exact Or.inr (Or.inr ⟨a, X, hX, rfl, hle _ hz⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

@[simp] theorem ccEquiv_apply (x : (Cn A).Element) : ccEquiv x = toCC x := rfl

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `Cₐ` as an object of the `∅`-free category. -/
abbrev Cnobj (A : Type) [DecidableEq A] : StrictDomainObj.{0} := ⟨Strn A, Cn A, Cn_nonempty⟩

end Algebra
end

section
variable {A : Type} [DecidableEq A]

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

@[simp] theorem Cnobj_sys (A : Type) [DecidableEq A] : (Cnobj A).sys = Cn A := rfl

end Algebra
end

section
variable {A : Type} [DecidableEq A]

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **The `Tsig`-algebra structure on `Cₐ`.** The structure map `i : 𝟙+Σ_a Cₐ → Cₐ` is the inverse of
the domain-equation isomorphism `ccEquiv`, strict by `isStrict_ofIso`. -/
abbrev cnStr : (((Tsig A).obj (Cnobj A)) ⟶ (Cnobj A)) :=
  ⟨ofIso ccEquiv.symm, isStrict_ofIso _⟩

end Algebra
end

section
variable {A : Type} [DecidableEq A]

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- **`Cₐ` is a `Tsig`-algebra** for `Tsig(X) = 𝟙 + Σ_a X`. -/
abbrev Cnalg (A : Type) [DecidableEq A] [Inhabited A] : TAlgebra (Tsig A) := ⟨Cnobj A, cnStr⟩

end Algebra
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem consMapN_mem_embA {a : A} {z : (Cn A).Element} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    ((consMapN a).toElementMap z).mem (embA a X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', -, -, hsub⟩
    rw [← embA_eq_prependN] at hsub
    exact z.up_mem hzX' hX (embA_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memCn_embA a hX, ?_⟩
    rw [← embA_eq_prependN]

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem consMapN_not_mem_embA_ne {a c : A} (hac : a ≠ c) {z : (Cn A).Element} {X : Set (Strn A)} :
    ¬ ((consMapN a).toElementMap z).mem (embA c X) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  obtain ⟨w, hw, -⟩ := hsub ⟨t, rfl, ht⟩
  rw [List.cons.injEq] at hw; exact hac hw.1

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

omit [Inhabited A] in

theorem consMapN_not_mem_nil {a : A} {z : (Cn A).Element} :
    ¬ ((consMapN a).toElementMap z).mem ({[]} : Set (Strn A)) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  have hmem := hsub ⟨t, rfl, ht⟩
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The distinguished point `e = k(inj_𝟙)`: the image under `k` of the terminator. -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjU (h := B.carrier.nonempty))

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The `a`-th successor operation `f_a = k ∘ inj_a`. -/
def descF (a : A) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjC (h := B.carrier.nonempty) a y)

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem descF_mono (a : A) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B a y ≤ descF B a y' :=
  B.str.1.toElementMap_mono (sinjC_mono h)

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The recursion `φ(Λ)=z`, `φ(a·σ)=f_a(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Strn A → B.carrier.sys.Element
  | [] => z
  | a :: σ => descF B a (descVal z σ)

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Strn A) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons a σ ih => exact congrArg (descF B a) ih

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem descMap_hcone {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem descMap_hsing {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

omit [Inhabited A] in
/-- Two maps out of `Cₐ` agree once they agree on every `σ⊥` and `σ` (generic `Exercise516.map_ext_C`). -/
theorem map_ext_Cn {V : NeighborhoodSystem β} {f g : ApproximableMap (Cn A) V}
    (hbot : ∀ σ, f.toElementMap (strBotN σ) = g.toElementMap (strBotN σ))
    (helem : ∀ σ, f.toElementMap (strElemN σ) = g.toElementMap (strElemN σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (Cn_mem.mp hX)
  · exact hbot σ
  · exact helem σ

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

omit [DecidableEq A] in
/-- A cone is never contained in a singleton: it has the two distinct elements `τ` and `τ·default`. -/
theorem not_coneN_subset_singleton (τ σ : Strn A) : ¬ coneN τ ⊆ ({σ} : Set (Strn A)) := by
  intro h
  have h1 : τ ∈ ({σ} : Set (Strn A)) := h (show τ ∈ coneN τ from List.prefix_rfl)
  have h2 : (τ ++ [default]) ∈ ({σ} : Set (Strn A)) := h (List.prefix_append τ [default])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [default] := h1.trans h2.symm
  simp at this

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

omit [DecidableEq A] in

theorem coneN_ne_singleton (τ σ : Strn A) : coneN τ ≠ ({σ} : Set (Strn A)) := fun h =>
  not_coneN_subset_singleton τ σ (h ▸ subset_rfl)

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

/-- A map `Cₐ → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`. (The alphabet-generic copy of `Exercise419.liftC`.) -/
def liftCn (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap (Cn A) V where
  rel X Y := (∃ σ, X = coneN σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memCn_coneN σ
    · exact memCn_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [Cn_master]; exact coneN_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have hσσ : σ = σ' := coneN_injective hX'
      subst hσσ
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (coneN_ne_singleton σ σ')
    · exact absurd hX'.symm (coneN_ne_singleton σ' σ)
    · have hσσ : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst hσσ
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · have hpre : σ <+: τ := coneN_subset_coneN.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · have hpre : σ <+: τ := singleton_subset_coneN.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_coneN_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have hmem := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at hmem
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **The homomorphism `Cₐ → E`**, built by `liftCn` from the head-recursion. -/
def descMap : ApproximableMap (Cn A) B.carrier.sys :=
  liftCn B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

theorem liftCn_strBot (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strBotN σ) = coneVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := coneN_subset_coneN.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_coneN_subset_singleton σ σ')
  · intro hY
    exact ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

@[simp] theorem descMap_strBot (σ : Strn A) :
    (descMap B).toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ :=
  liftCn_strBot _ _ _ _ _ σ

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

theorem liftCn_strElem (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strElemN σ) = singVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_coneN.mp; rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have hmem := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at hmem
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

end Lift
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

@[simp] theorem descMap_strElem (σ : Strn A) :
    (descMap B).toElementMap (strElemN σ) = descVal B (descE B) σ :=
  liftCn_strElem _ _ _ _ _ σ

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem Cn_bot_eq_strBotN_nil : (Cn A).bot = strBotN ([] : Strn A) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show ((Cn A).mem Y ∧ (Cn A).master ⊆ Y) ↔ ((Cn A).mem Y ∧ coneN [] ⊆ Y)
  rw [Cn_master, coneN_nil]

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

theorem ccEquiv_comp_symm :
    (ofIso (ccEquiv (A := A))).comp (ofIso ccEquiv.symm) = idMap (CCn A) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

theorem ccEquiv_symm_comp :
    (ofIso (ccEquiv (A := A)).symm).comp (ofIso ccEquiv) = idMap (Cn A) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, Cn_bot_eq_strBotN_nil, descMap_strBot]
  rfl

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The bundled strict homomorphism `Cₐ → E`. -/
def descStrict : ((Cnobj A) ⟶ B.carrier) := ⟨descMap B, descMap_strict B⟩

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

theorem genKeyBot (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strBotN ([] : Strn A))))
      = B.carrier.sys.bot := by
  have hb : toCC (strBotN ([] : Strn A)) = (CCn A).bot := by
    rw [← Cn_bot_eq_strBotN_nil, ← ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMapSig (A := A) (h₀ := Cn_nonempty)
    (h₁ := B.carrier.nonempty) g)]
  exact isStrict_iff_apply_bot.mp B.str.2

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]
omit [Inhabited A] in

/-- **`toCC ∘ (a·) = inj_a`.** Prepending the letter `a` to `z` is, across `Cₐ ≅ 𝟙+Σ_a Cₐ`, the
injection of `z` into the `a`-th summand. -/
theorem toCC_consMapN (a : A) (z : (Cn A).Element) :
    toCC ((consMapN a).toElementMap z) = sinjC (h := Cn_nonempty) a z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨c, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact absurd hz consMapN_not_mem_nil
    · by_cases hac : a = c
      · subst hac; exact Or.inr ⟨X, hX, rfl, (consMapN_mem_embA hX).mp hz⟩
      · exact absurd hz (consMapN_not_mem_embA_ne hac)
  · rintro (rfl | ⟨X, hX, rfl, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (consMapN_mem_embA hX).mpr hm⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem genKey (g : ApproximableMap (Cn A) B.carrier.sys) (a : A) (w : (Cn A).Element) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC ((consMapN a).toElementMap w)))
      = descF B a (g.toElementMap w) := by
  rw [toCC_consMapN, sumMapSig_sinjC]; rfl

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]
omit [Inhabited A] in

/-- **`toCC Λ̂ = inj_𝟙`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElemN_nil :
    toCC (strElemN ([] : Strn A)) = sinjU (h := Cn_nonempty) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, memCn_singleton [], subset_rfl⟩)

end Iso
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

omit [Inhabited A] in

theorem genKey0 (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strElemN ([] : Strn A))))
      = descE B := by
  rw [toCC_strElemN_nil, sumMapSig_sinjU]; rfl

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- `Cₐ`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_Cn
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strBot]
      have h := genKey B (descMap B) a (strBotN σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strElem]
      have h := genKey B (descMap B) a (strElemN σ)
      rw [descMap_strElem] at h
      exact h.symm

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **The homomorphism square** `desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **The descent homomorphism `(Cₐ, i) → (E, k)`** as a `Tsig`-algebra homomorphism. -/
def descAlgHom : AlgHom (Cnalg A) B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** -/
theorem rec_determines (g : ApproximableMap (Cn A) B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKeyBot B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strBot]
      have h := genKey B g a (strBotN σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElemN σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKey0 B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strElem]
      have h := genKey B g a (strElemN σ)
      rw [ih] at h
      exact h
  apply map_ext_Cn
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

end Initial
end

section
variable {A : Type} [DecidableEq A]

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- **Uniqueness.** Any `Tsig`-algebra homomorphism out of `(Cₐ, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom (Cnalg A) B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty) hom.1) := by
      exact congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial
end

section
variable {A : Type} [DecidableEq A]

/-- **Exercise 6.17 part 2 — `(Cₐ, i)` is an initial `Tsig`-algebra for `Tsig(X) = 𝟙 + Σ_a X`.**
The descent map `φ : Cₐ → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(a·x) = f_a(φ x)`
(`f_a = k ∘ inj_a`), built choice-free via `liftCn`; it is the unique `Tsig`-algebra homomorphism, so
`Cₐ` is the initial algebra of `X ↦ 𝟙 + Σ_a X`. -/
def CnisInitial (A : Type) [DecidableEq A] [Inhabited A] : IsInitial (Cnalg A) where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h
end

section
variable {A : Type} [DecidableEq A]

/-- **`Cₙ` is the initial algebra** of `X ↦ 𝟙 + Σ_{Fin (n+1)} X`. -/
def CfinIsInitial (n : ℕ) : IsInitial (Cnalg (Fin (n + 1))) := CnisInitial (Fin (n + 1))
end

section
variable {A : Type} [DecidableEq A]

/-- **Exercise 6.17 part 2 — the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
theorem Cn_domain_equation (A : Type) [DecidableEq A] [Inhabited A] :
    Cn A ≅ᴰ CCn A := ⟨ccEquiv⟩
end

section
set_option linter.unusedVariables false

theorem example_617_gen : ∀ (A : Type) [inst : DecidableEq A] [Inhabited A],
  @DomainTheory.NeighbourhoodSystems.Isomorphic (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A)
    (DomainTheory.NeighbourhoodSystems.Exercise617Gen.SigTok A
      (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A))
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn A inst)
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.CCn A inst) :=
  DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn_domain_equation
end

section
variable {A : Type} [DecidableEq A]

/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))
end

section
variable {A : Type}

section Iso

theorem embA_ne {a a' : A} (h : a ≠ a') {X Y : Set (Strn A)} (hX : X.Nonempty) :
    embA a X ≠ embA a' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (a :: w') ∈ embA a' Y := heq ▸ (⟨w', rfl, hw'⟩ : (a :: w') ∈ embA a X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he; exact h he.1

end Iso
end

section
variable {A : Type}

section Iso

theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

end Iso
end

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The "cons" of a head `a : |𝒟|` and a tail `b : |𝒟^∞|`, as a sequence `⟨a, b₀, b₁, …⟩`. -/
def consSeq (a : V.Element) (b : (iterSys V).Element) : ℕ → V.Element :=
  fun i => Nat.casesOn i a (fun k => component b k)

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

@[simp] theorem consSeq_zero (a : V.Element) (b : (iterSys V).Element) : consSeq a b 0 = a := rfl

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

@[simp] theorem consSeq_succ (a : V.Element) (b : (iterSys V).Element) (k : ℕ) :
    consSeq a b (k + 1) = component b k := rfl

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `⊥` of `𝒟^∞` is the all-`⊥` sequence. -/
theorem iterBot_eq : (iterSys V).bot = ofSeq (fun _ : ℕ => V.bot) := by
  apply Element.ext
  intro W
  rw [mem_bot, mem_ofSeq]
  constructor
  · rintro rfl
    refine ⟨(iterSys V).master_mem, fun i => ?_⟩
    rw [fiber_iterSys_master, mem_bot]
  · rintro ⟨_, hfib⟩
    apply eq_of_fiber_eq
    intro i
    have hi := hfib i
    rw [fiber_iterSys_master]
    rwa [mem_bot] at hi

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The `n`-th coordinate of `⊥` is `⊥`. -/
@[simp] theorem component_bot (n : ℕ) : component (iterSys V).bot n = V.bot := by
  rw [iterBot_eq, component_ofSeq]

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- A successor-increasing chain is increasing. -/
theorem chain_le_of_succ {β : Type*} {W : NeighborhoodSystem β} {a : ℕ → W.Element}
    (h : ∀ n, a n ≤ a (n + 1)) {i j : ℕ} (hij : i ≤ j) : a i ≤ a j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (h _)

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The bottom map is below everything. -/
theorem constBot_le (f : ApproximableMap (iterSys V) E) :
    constMap (iterSys V) E.bot ≤ f := by
  intro X Y hrel
  obtain ⟨hX, hY⟩ := hrel
  rw [mem_bot] at hY; subst hY
  exact f.rel_master hX

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `i : 𝒟 × 𝒟^∞ → 𝒟^∞`, the "cons" iso (`iterProdIso⁻¹`); the `T`-algebra structure map. -/
def imap (V : NeighborhoodSystem α) : ApproximableMap (prod V (iterSys V)) (iterSys V) :=
  ofIso (iterProdIso V).symm

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

theorem isStrict_imap : IsStrict (imap V) := isStrict_ofIso _

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The forward iso reads off head and tail.** `iterProdIso z = ⟨z₀, ⟨z₁,z₂,…⟩⟩`: the first
component is the `0`-coordinate `component z 0`, the second is the shifted sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The inverse iso is "cons".** `iterProdIso⁻¹ ⟨a, b⟩ = ⟨a, b₀, b₁, …⟩`. -/
theorem iterProdIso_symm_pair (a : V.Element) (b : (iterSys V).Element) :
    (iterProdIso V).symm (pair a b) = ofSeq (consSeq a b) := by
  have hkey : iterProdIso V (ofSeq (consSeq a b)) = pair a b := by
    rw [iterProdIso_apply]
    congr 1
    · rw [component_ofSeq, consSeq_zero]
    · have : (fun n => component (ofSeq (consSeq a b)) (n + 1)) = fun n => component b n := by
        funext n; rw [component_ofSeq, consSeq_succ]
      rw [this, ofSeq_component]
  rw [← hkey, OrderIso.symm_apply_apply]

end Exercise618
end

section
namespace Exercise618

/-- The infinite iterate of an `∅`-free system is `∅`-free (each fibre is a non-empty neighbourhood). -/
theorem iterSys_nonempty {α : Type*} {V : NeighborhoodSystem α}
    (h : ∀ X, V.mem X → X.Nonempty) :
    ∀ W, (iterSys V).mem W → W.Nonempty := by
  rintro W ⟨hfib, _⟩
  obtain ⟨a, ha⟩ := h (fiber W 0) (hfib 0)
  exact ⟨(0, a), ha⟩

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `𝒟^∞` (Exercise 3.16's `iterSys`) as an `∅`-free object. -/
def iterObj (Dom : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := ℕ × Dom.carrier
  sys := iterSys Dom.sys
  nonempty := iterSys_nonempty Dom.nonempty

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `j : 𝒟^∞ → 𝒟 × 𝒟^∞`, the splitting iso (`iterProdIso`). -/
def jmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (prod V (iterSys V)) :=
  ofIso (iterProdIso V)

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The homomorphism operator `Op(f) = k ∘ T(f) ∘ j`. -/
def descOp (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E) :
    ApproximableMap (iterSys V) E :=
  k.comp ((prodMap (idMap V) f).comp (jmap V))

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The defining action of the operator: `Op(f)(z) = k(z₀, f(⟨z₁,z₂,…⟩))`. -/
theorem descOp_apply (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E)
    (z : (iterSys V).Element) :
    (descOp k f).toElementMap z
      = k.toElementMap (pair (component z 0)
          (f.toElementMap (ofSeq (fun n => component z (n + 1))))) := by
  simp only [descOp, jmap]
  rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, iterProdIso_apply,
    toElementMap_prodMap_pair, toElementMap_idMap]

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain `h₀ = ⊥`, `hₙ₊₁ = Op(hₙ)`. -/
def descSeq (k : ApproximableMap (prod V E) E) : ℕ → ApproximableMap (iterSys V) E
  | 0 => constMap (iterSys V) E.bot
  | (n + 1) => descOp k (descSeq k n)

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **`g`-independence step.** If `g` is a homomorphism (`g ∘ i = k ∘ T(g)`) then
`g ∘ ρₙ₊₁ = k ∘ T(g ∘ ρₙ) ∘ j = Op_k(g ∘ ρₙ)`: the composite depends only on `g ∘ ρₙ`. -/
theorem gcomp_rho_succ (k : ApproximableMap (prod V E) E) (g : ApproximableMap (iterSys V) E)
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g)) (n : ℕ) :
    g.comp (descSeq (imap V) (n + 1)) = descOp k (g.comp (descSeq (imap V) n)) := by
  show g.comp ((imap V).comp ((prodMap (idMap V) (descSeq (imap V) n)).comp (jmap V)))
     = k.comp ((prodMap (idMap V) (g.comp (descSeq (imap V) n))).comp (jmap V))
  rw [← comp_assoc, hc, comp_assoc]
  congr 1
  rw [← comp_assoc, ← prodMap_comp, idMap_comp]

end Uniq

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain for any strict `g` starts at the constant `⊥`: `g ∘ ρ₀ = ⊥`. -/
theorem gcomp_rho_zero (g : ApproximableMap (iterSys V) E) (hg : IsStrict g) :
    g.comp (descSeq (imap V) 0) = constMap (iterSys V) E.bot := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_constMap,
    show descSeq (imap V) 0 = constMap (iterSys V) (iterSys V).bot from rfl,
    toElementMap_constMap, isStrict_iff_apply_bot.mp hg]

end Uniq

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `j ∘ i = I` on `𝒟 × 𝒟^∞`. -/
theorem jmap_comp_imap : (jmap V).comp (imap V) = idMap (prod V (iterSys V)) := by
  apply ext_of_toElementMap
  intro w
  simp only [jmap, imap]
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The continuity helper `k(a, ·) : E → E` as an approximable map. -/
def kHead (k : ApproximableMap (prod V E) E) (a : V.Element) :
    ApproximableMap E E :=
  k.comp (paired (constMap E a) (idMap E))

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem kHead_apply (k : ApproximableMap (prod V E) E) (a : V.Element) (u : E.Element) :
    (kHead k a).toElementMap u = k.toElementMap (pair a u) := by
  rw [kHead, toElementMap_comp, toElementMap_paired, toElementMap_constMap, toElementMap_idMap]

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `⊥` of a product is the pair of `⊥`s. -/
theorem pair_bot {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} :
    pair V₀.bot V₁.bot = (prod V₀ V₁).bot := by
  apply Element.ext
  intro W
  rw [mem_bot, prod_master]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY; subst hX; subst hY; rfl
  · rintro rfl
    exact ⟨V₀.master, V₁.master, V₀.bot.master_mem, V₁.bot.master_mem, rfl⟩

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    ∀ n, IsStrict (descSeq k n)
  | 0 => isStrict_constBot
  | (n + 1) => by
      have ih := descSeq_strict k hk n
      rw [isStrict_iff_apply_bot] at ih ⊢
      rw [show descSeq k (n + 1) = descOp k (descSeq k n) from rfl, descOp_apply]
      have htl : ofSeq (fun m => component (iterSys V).bot (m + 1)) = (iterSys V).bot := by
        have hconst : (fun m => component (iterSys V).bot (m + 1)) = (fun _ => V.bot) := by
          funext m; rw [component_bot]
        rw [hconst, ← iterBot_eq]
      rw [component_bot, htl, ih, pair_bot]
      exact isStrict_iff_apply_bot.mp hk

end Target

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `T(f₀ × f₁)` is strict when both factors are: `(f₀ × f₁)(⊥,⊥) = (f₀ ⊥, f₁ ⊥) = (⊥,⊥)`. -/
theorem isStrict_prodMap {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {f₀ : ApproximableMap V₀ V₀'} {f₁ : ApproximableMap V₁ V₁'}
    (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) : IsStrict (prodMap f₀ f₁) := by
  rw [isStrict_iff_apply_bot, show (prod V₀ V₁).bot = pair V₀.bot V₁.bot from pair_bot.symm,
    toElementMap_prodMap_pair, isStrict_iff_apply_bot.mp hf₀, isStrict_iff_apply_bot.mp hf₁]
  exact pair_bot

end Exercise618
end

section
namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

end Exercise618
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise618
section
set_option linter.unusedVariables false

theorem example_618.{u_2, u_3, u_4, u_5} : ∀ {α : Type u_2} {β : Type u_3} {α' : Type u_4} {β' : Type u_5}
  {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
  {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
  {f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
  {f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α' V₀ V₀' f₀ →
    @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict β β' V₁ V₁' f₁ →
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f₀ f₁) :=
  @DomainTheory.NeighbourhoodSystems.Exercise618.isStrict_prodMap
end

end DomainTheory.NeighbourhoodSystems.Exercise618
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- `T(·) = (id_𝒟 × ·)` is monotone. -/
theorem prodMap_idMap_mono {γ : Type*} {E : NeighborhoodSystem γ}
    {f f' : ApproximableMap (iterSys V) E} (h : f ≤ f') :
    prodMap (idMap V) f ≤ prodMap (idMap V) f' := by
  intro W P hrel
  simp only [prodMap, paired_rel] at hrel ⊢
  exact ⟨hrel.1, hrel.2.1, comp_mono_gen h le_rfl _ _ hrel.2.2⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descOp_mono (k : ApproximableMap (prod V E) E) {f f' : ApproximableMap (iterSys V) E}
    (h : f ≤ f') : descOp k f ≤ descOp k f' :=
  comp_mono_gen le_rfl (comp_mono_gen (prodMap_idMap_mono h) le_rfl)

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_mono_succ (k : ApproximableMap (prod V E) E) (n : ℕ) :
    descSeq k n ≤ descSeq k (n + 1) := by
  induction n with
  | zero => exact constBot_le _
  | succ m ih => exact descOp_mono k ih

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_mono (k : ApproximableMap (prod V E) E) {n m : ℕ} (h : n ≤ m) :
    descSeq k n ≤ descSeq k m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descSeq_mono_succ k _)

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descSeq_dir (k : ApproximableMap (prod V E) E) :
    ∀ i j, ∃ l, (∀ X Y, (descSeq k i).rel X Y → (descSeq k l).rel X Y) ∧
      (∀ X Y, (descSeq k j).rel X Y → (descSeq k l).rel X Y) :=
  fun i j => ⟨max i j, fun _ _ => descSeq_mono k (le_max_left i j) _ _,
    fun _ _ => descSeq_mono k (le_max_right i j) _ _⟩

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **The descent map `h = ⋃ₙ hₙ : 𝒟^∞ → E`.** -/
def descMap (k : ApproximableMap (prod V E) E) : ApproximableMap (iterSys V) E :=
  iSupMap (descSeq k) (descSeq_dir k)

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descMap_toElementMap (k : ApproximableMap (prod V E) E) (z : (iterSys V).Element)
    {Y : Set γ} :
    ((descMap k).toElementMap z).mem Y ↔ ∃ n, ((descSeq k n).toElementMap z).mem Y :=
  mem_toElementMap_iSupMap (descSeq k) (descSeq_dir k) z

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

theorem descMap_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    IsStrict (descMap k) := by
  rw [isStrict_iff_apply_bot]
  apply Element.ext
  intro Y
  rw [mem_bot, descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hs := descSeq_strict k hk n
    rw [isStrict_iff_apply_bot] at hs
    rw [hs, mem_bot] at hn
    exact hn
  · rintro rfl
    have hs := descSeq_strict k hk 0
    rw [isStrict_iff_apply_bot] at hs
    exact ⟨0, by rw [hs]; exact E.bot.master_mem⟩

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

/-- The product of two `∅`-free systems is `∅`-free. -/
theorem prod_nonempty {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (_h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ∀ W, (prod V₀ V₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, hX, _, rfl⟩
  obtain ⟨a, ha⟩ := h₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The fixed domain `𝒟` times an object `X`, again an `∅`-free domain. -/
def prodObj (Dom X : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Dom.carrier ⊕ X.carrier
  sys := prod Dom.sys X.sys
  nonempty := prod_nonempty Dom.nonempty X.nonempty

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The morphism action `T(f) = id_𝒟 × f`, strict by `isStrict_prodMap`. -/
def prodMapHom (Dom : StrictDomainObj.{w}) {X Y : StrictDomainObj.{w}} (f : (X ⟶ Y)) :
    ((prodObj Dom X) ⟶ (prodObj Dom Y)) :=
  ⟨prodMap (idMap Dom.sys) f.1, isStrict_prodMap isStrict_idMap f.2⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The product endofunctor `T(X) = 𝒟 × X`** on `∅`-free domains and strict maps, for a fixed
domain `𝒟`. On objects `T(X) = 𝒟 × X`; on maps `T(f) = id_𝒟 × f`. -/
def prodFunctor (Dom : StrictDomainObj.{w}) : Endofunctor StrictDomainObj.{w} where
  obj := prodObj Dom
  map := prodMapHom Dom
  map_id X := Subtype.ext (by
    show prodMap (idMap Dom.sys) (idMap X.sys) = idMap (prod Dom.sys X.sys)
    exact prodMap_id)
  map_comp {X Y Z} g f := Subtype.ext (by
    show prodMap (idMap Dom.sys) (g.1.comp f.1)
       = (prodMap (idMap Dom.sys) g.1).comp (prodMap (idMap Dom.sys) f.1)
    have h := prodMap_comp (idMap Dom.sys) (idMap Dom.sys) g.1 f.1
    rw [idMap_comp] at h
    exact h)

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **`𝒟^∞` as a `T`-algebra**, `(𝒟^∞, i)` with `i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" iso (`imap`,
Exercise 3.16's `iterProdIso⁻¹`), strict by `isStrict_imap`. -/
def iterAlg (Dom : StrictDomainObj.{w}) : TAlgebra (prodFunctor Dom) where
  carrier := iterObj Dom
  str := ⟨imap Dom.sys, isStrict_imap⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The truncation formula** `ρₙ(⟨x₀,x₁,…⟩) = ⟨x₀,…,x_{n-1},⊥,⊥,…⟩`. -/
theorem rho_apply (n : ℕ) (z : (iterSys V).Element) :
    (descSeq (imap V) n).toElementMap z
      = ofSeq (fun i => if i < n then component z i else V.bot) := by
  induction n generalizing z with
  | zero =>
    show (constMap (iterSys V) (iterSys V).bot).toElementMap z = _
    rw [toElementMap_constMap, iterBot_eq]
    congr 1
  | succ n ih =>
    rw [show descSeq (imap V) (n + 1) = descOp (imap V) (descSeq (imap V) n) from rfl,
      descOp_apply, ih]
    simp only [imap]
    rw [toElementMap_ofIso, iterProdIso_symm_pair]
    congr 1
    funext j
    cases j with
    | zero =>
      show component z 0 = if (0 : ℕ) < n + 1 then component z 0 else V.bot
      rw [ite_eq_left (Nat.zero_lt_succ n)]
    | succ k =>
      rw [consSeq_succ, component_ofSeq, component_ofSeq]
      show (if k < n then component z (k + 1) else V.bot)
         = if k + 1 < n + 1 then component z (k + 1) else V.bot
      by_cases h : k < n
      · rw [ite_eq_left h, ite_eq_left (Nat.succ_lt_succ h)]
      · rw [ite_eq_right h, ite_eq_right (fun hc => h (Nat.lt_of_succ_lt_succ hc))]

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **`⋃ₙ ρₙ = I`.** Every `z` is the directed union of its truncations: the cofinite-`Δ` structure
of `𝒟^∞` means each neighbourhood of `z` is already realised by a finite truncation. -/
theorem iSupRho_eq_id : descMap (imap V) = idMap (iterSys V) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_idMap]
  apply Element.ext
  intro Y
  rw [descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hle : (descSeq (imap V) n).toElementMap z ≤ z := by
      rw [rho_apply]
      have hz : z = ofSeq (fun i => component z i) := (ofSeq_component z).symm
      conv_rhs => rw [hz]
      apply ofSeq_mono
      intro i
      show (if i < n then component z i else V.bot) ≤ component z i
      split
      · exact le_rfl
      · exact V.bot_le _
    exact hle Y hn
  · intro hzY
    have hY : (iterSys V).mem Y := z.sub hzY
    obtain ⟨N, hN⟩ := hY.2
    have hcomp : ∀ i, (component z i).mem (fiber Y i) := by
      have h := hzY
      rw [← ofSeq_component z] at h
      rw [mem_ofSeq] at h
      exact h.2
    refine ⟨N, ?_⟩
    rw [rho_apply, mem_ofSeq]
    refine ⟨hY, fun i => ?_⟩
    show (if i < N then component z i else V.bot).mem (fiber Y i)
    by_cases h : i < N
    · rw [ite_eq_left h]; exact hcomp i
    · rw [ite_eq_right h, hN i (not_lt.mp h)]; exact V.bot.master_mem

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **Uniqueness.** Any two strict homomorphisms `g, g' : 𝒟^∞ → E` into a `T`-algebra `(E,k)` are
equal. By `g`-independence they agree on every truncation (`g ∘ ρₙ = g' ∘ ρₙ`), and `⋃ₙ ρₙ = I`
forces `g = g'`. -/
theorem comm_unique (k : ApproximableMap (prod V E) E)
    {g g' : ApproximableMap (iterSys V) E} (hg : IsStrict g) (hg' : IsStrict g')
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g))
    (hc' : g'.comp (imap V) = k.comp (prodMap (idMap V) g')) : g = g' := by
  have hindep : ∀ n, g.comp (descSeq (imap V) n) = g'.comp (descSeq (imap V) n) := by
    intro n
    induction n with
    | zero => rw [gcomp_rho_zero g hg, gcomp_rho_zero g' hg']
    | succ m ih => rw [gcomp_rho_succ k g hc m, gcomp_rho_succ k g' hc' m, ih]
  have key : g.comp (descMap (imap V)) = g'.comp (descMap (imap V)) := by
    apply ApproximableMap.ext
    intro X Z
    simp only [descMap, comp_rel]
    constructor
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg : (g.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [hindep i] at hg
      obtain ⟨Y', hXY', hYZ'⟩ := hg
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg' : (g'.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [← hindep i] at hg'
      obtain ⟨Y', hXY', hYZ'⟩ := hg'
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
  rw [iSupRho_eq_id] at key
  rwa [comp_idMap, comp_idMap] at key

end Uniq

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- Directedness of a successor-increasing chain. -/
theorem succChainDir {β : Type*} {W : NeighborhoodSystem β} (a : ℕ → W.Element)
    (h : ∀ n, a n ≤ a (n + 1)) : ∀ i j, ∃ l, a i ≤ a l ∧ a j ≤ a l :=
  fun i j => ⟨max i j, chain_le_of_succ h (le_max_left i j), chain_le_of_succ h (le_max_right i j)⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- Approximable maps are monotone in the map argument: `f ≤ g ⟹ f(x) ≤ g(x)`. -/
theorem toElementMap_le_of_le {β₀ β₁ : Type*} {W₀ : NeighborhoodSystem β₀}
    {W₁ : NeighborhoodSystem β₁} {f g : ApproximableMap W₀ W₁} (h : f ≤ g) (x : W₀.Element) :
    f.toElementMap x ≤ g.toElementMap x := by
  rintro Y ⟨X, hX, hrel⟩
  exact ⟨X, hX, h _ _ hrel⟩

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain is increasing element-wise. -/
theorem descSeqEltMono (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    ∀ n, (descSeq k n).toElementMap x ≤ (descSeq k (n + 1)).toElementMap x :=
  fun n => toElementMap_le_of_le (descSeq_mono_succ k n) x

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **The descent map as a directed union.** `h(x) = ⋃ₙ hₙ(x)`. -/
theorem descMap_eq (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    (descMap k).toElementMap x
      = iSupDirected (fun n => (descSeq k n).toElementMap x)
          (succChainDir _ (descSeqEltMono k x)) := by
  apply Element.ext
  intro Y
  rw [descMap_toElementMap, mem_iSupDirected]

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **The descent map is a fixed point** of `Op = k ∘ T(·) ∘ j`. -/
theorem descMap_fix (k : ApproximableMap (prod V E) E) : descMap k = descOp k (descMap k) := by
  apply ext_of_toElementMap
  intro z
  rw [descOp_apply, descMap_eq k (ofSeq (fun n => component z (n + 1))),
    ← kHead_apply k (component z 0), toElementMap_iSupDirected, descMap_eq k z]
  -- both sides are directed unions; compare the (reindexed) families term-wise
  apply Element.ext
  intro Y
  rw [mem_iSupDirected, mem_iSupDirected]
  have hstep : ∀ m, (kHead k (component z 0)).toElementMap
        ((descSeq k m).toElementMap (ofSeq (fun n => component z (n + 1))))
      = (descSeq k (m + 1)).toElementMap z := by
    intro m
    rw [kHead_apply, show descSeq k (m + 1) = descOp k (descSeq k m) from rfl, descOp_apply]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact ⟨0, by rw [hstep 0]; exact descSeqEltMono k z 0 _ hn⟩
    | succ m => exact ⟨m, by rw [hstep m]; exact hn⟩
  · rintro ⟨m, hm⟩
    rw [hstep m] at hm
    exact ⟨m + 1, hm⟩

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **Existence of the algebra homomorphism.** The descent map makes the square commute:
`descMap ∘ i = k ∘ T(descMap)` (using `j ∘ i = I` and the fixed-point equation). -/
theorem descMap_comm (k : ApproximableMap (prod V E) E) :
    (descMap k).comp (imap V) = k.comp (prodMap (idMap V) (descMap k)) := by
  conv_lhs => rw [descMap_fix k]
  show (k.comp ((prodMap (idMap V) (descMap k)).comp (jmap V))).comp (imap V)
     = k.comp (prodMap (idMap V) (descMap k))
  rw [comp_assoc, comp_assoc, jmap_comp_imap, comp_idMap]

end Target

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The descent homomorphism `(𝒟^∞, i) → (E, k)`**: the strict map `descMap k` (existence half),
with the homomorphism square supplied by `descMap_comm`. -/
def descAlgHom (Dom : StrictDomainObj.{w}) (B : TAlgebra (prodFunctor Dom)) :
    AlgHom (iterAlg Dom) B where
  hom := ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩
  comm := by
    apply Subtype.ext
    show (descMap B.str.1).comp (imap Dom.sys)
       = B.str.1.comp (prodMap (idMap Dom.sys) (descMap B.str.1))
    exact descMap_comm B.str.1

end Exercise618
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/- concordance: source L4079 EXERCISE 6.18 infinite product as initial -/
/-- **Exercise 6.18 (initial-algebra half) — `𝒟^∞` is the initial `T`-algebra for `T(X) = 𝒟 × X`.**
For every `T`-algebra `(E, k)` the descent map `h(⟨x₀,x₁,…⟩) = k(x₀, k(x₁, …))` is the *unique*
strict homomorphism `𝒟^∞ → E`. Together with Exercise 3.16's `𝒟^∞ ≅ 𝒟 × 𝒟^∞` (the domain-equation
half), this exhibits `𝒟^∞` both as the canonical solution of the domain equation and as the initial
algebra (determined up to iso by Proposition 6.6). -/
def iterIsInitial (Dom : StrictDomainObj.{w}) : IsInitial (iterAlg Dom) where
  desc := descAlgHom Dom
  uniq B h := by
    obtain ⟨hom, comm⟩ := h
    have hcomm : hom.1.comp (imap Dom.sys)
        = B.str.1.comp (prodMap (idMap Dom.sys) hom.1) := congrArg Subtype.val comm
    have hg : hom.1 = descMap B.str.1 :=
      comm_unique B.str.1 hom.2 (descMap_strict B.str.1 B.str.2) hcomm (descMap_comm B.str.1)
    have hhom : hom = ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩ := Subtype.ext hg
    subst hhom
    rfl

end Exercise618
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- **Example 6.1 — the forward half of the domain equation.** Sends an element `z` of `D^§` to an
element of `D + (D^§ × D^§)`, recording for each branch which `0X`/`1V` neighbourhoods `z` reaches:
`0X ∈ toS z ↔ embZero X ∈ z` and `1(P∪Q) ∈ toS z ↔ (1P∪2Q) ∈ z`. -/
def toS (z : (Dsharp D hD).Element) : (sumSys D hD).Element where
  mem W := W = sumMaster D (prod (Dsharp D hD) (Dsharp D hD))
    ∨ (∃ X, D.mem X ∧ W = inj₀ X ∧ z.mem (embZero X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = inj₁ (prodNbhd P Q) ∧ z.mem (embPair P Q))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨prodNbhd P Q, prod_mem_prodNbhd hP hQ, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨P', Q', hP', hQ', rfl, hzPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [sumMaster_inter_inj₁ (prod_mem_prodNbhd hP' hQ')], hzPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embZero_inter] at hz
        exact memS_embZero_inv hD (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embZero_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzPQ'; rw [embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (prod_mem_prodNbhd hP hQ)], hzPQ⟩)
    · exfalso
      have hz := z.inter_mem hzPQ hzX'; rw [Set.inter_comm, embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [inj₁_inter, prodNbhd_inter], ?_⟩)
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).1
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).2
      · have hz := z.inter_mem hzPQ hzPQ'; rwa [embPair_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩) hW' hsub
    · left
      exact eq_sumMaster_of_subset hW' hsub
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemS.zero hX') (embZero_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · obtain ⟨a, ha⟩ := hD X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD (prodNbhd P Q) (prod_mem_prodNbhd hP hQ)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨P', Q', hP', hQ', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := prodNbhd_subset_iff.mp (inj₁_subset_inj₁.mp hsub)
        exact z.up_mem hzPQ (MemS.pair hP' hQ') (embPair_subset.mpr ⟨hPP, hQQ⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem toS_mem_inj₀ {z : (Dsharp D hD).Element} {X : Set α} (hX : D.mem X) :
    (toS D hD z).mem (inj₀ X) ↔ z.mem (embZero X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P, Q, hP, hQ, heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := hD X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem toS_mem_inj₁ {z : (Dsharp D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (toS D hD z).mem (inj₁ (prodNbhd P Q)) ↔ z.mem (embPair P Q) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P', Q', hP', hQ', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := hD X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · obtain ⟨hPP, hQQ⟩ := prodNbhd_injective (inj₁_injective heq)
      rw [hPP, hQQ]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hz⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

theorem embPair_ne_Gamma (P Q : Set (List Bool × α)) : embPair P Q ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : (([], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

theorem embZero_ne_Gamma (X : Set α) : embZero X ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem; exact absurd hmem.1 (by simp)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

theorem embZero_ne_embPair {X : Set α} (hX : D.mem X) (P Q : Set (List Bool × α)) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨a, ha⟩ := hD X hX
  have hmem : (([], a) : List Bool × α) ∈ embPair P Q := h ▸ (⟨rfl, ha⟩ : ([], a) ∈ embZero X)
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- **Example 6.1 — the inverse half of the domain equation.** Sends an element `s` of
`D + (D^§ × D^§)` back to an element of `D^§`. -/
def fromS (s : (sumSys D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D
    ∨ (∃ X, D.mem X ∧ W = embZero X ∧ s.mem (inj₀ X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = embPair P Q ∧ s.mem (inj₁ (prodNbhd P Q)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact MemS.gamma
    · exact MemS.zero hX
    · exact MemS.pair hP hQ
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨P', Q', hP', hQ', rfl, hsPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX',
        by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma hX')], hsX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [Set.inter_eq_right.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP') (memS_subset_gamma hQ'))], hsPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hX)], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embZero_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv D hD (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsPQ'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_eq_left.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))], hsPQ⟩)
    · exfalso
      have hs := s.inter_mem hsPQ hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [embPair_inter], ?_⟩)
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).1
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).2
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embZero_subset.mp hsub))
      | @pair P' Q' hP' hQ' =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        have hmem : (([], a) : List Bool × α) ∈ embPair P' Q' := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        have hz : t ∈ embZero X' := hsub ht
        exact hcons hz.1
      | @pair P' Q' hP' hQ' =>
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact s.up_mem hsPQ (Or.inr (Or.inr ⟨prodNbhd P' Q', prod_mem_prodNbhd hP' hQ', rfl⟩))
          (inj₁_subset_inj₁.mpr (prodNbhd_subset_iff.mpr ⟨hPP, hQQ⟩))

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem fromS_mem_embZero {s : (sumSys D hD).Element} {X : Set α} (hX : D.mem X) :
    (fromS D hD s).mem (embZero X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P, Q, hP, hQ, heq, hs⟩)
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rwa [embZero_injective heq]
    · exact absurd heq (embZero_ne_embPair D hD hX P Q)
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

@[simp] theorem fromS_mem_embPair {s : (sumSys D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (fromS D hD s).mem (embPair P Q) ↔ s.mem (inj₁ (prodNbhd P Q)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P', Q', hP', hQ', heq, hs⟩)
    · exact absurd h0 (embPair_ne_Gamma D hD P Q)
    · exact absurd heq.symm (embZero_ne_embPair D hD hX' P Q)
    · obtain ⟨hPP, hQQ⟩ := embPair_injective heq
      rw [hPP, hQQ]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hs⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- `fromS ∘ toS = id`. -/
theorem fromS_toS (z : (Dsharp D hD).Element) : fromS D hD (toS D hD z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact z.master_mem
    · exact (toS_mem_inj₀ D hD hX).mp hs
    · exact (toS_mem_inj₁ D hD hP hQ).mp hs
  · intro hW
    cases z.sub hW with
    | gamma => exact Or.inl rfl
    | @zero X hX => exact Or.inr (Or.inl ⟨X, hX, rfl, (toS_mem_inj₀ D hD hX).mpr hW⟩)
    | @pair P Q hP hQ => exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (toS_mem_inj₁ D hD hP hQ).mpr hW⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- Scott's injection `x^§ = {Γ} ∪ {0X ∣ X ∈ x}` of a `D`-element into `D^§`. -/
def inSharp (x : D.Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ X, x.mem X ∧ W = embZero X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact MemS.gamma
    · exact MemS.zero (x.sub hX)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma (x.sub hX'))]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma (x.sub hX))]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embZero_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' => exact Or.inr ⟨X', x.up_mem hX hX' (embZero_subset.mp hsub), rfl⟩
      | @pair P Q hP hQ =>
        exfalso
        obtain ⟨a, ha⟩ := hD X (x.sub hX)
        have hmem : (([], a) : List Bool × α) ∈ embPair P Q := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- Scott's pairing `⟨x, y⟩ = {Γ} ∪ {1P ∪ 2Q ∣ P ∈ x, Q ∈ y}` of two `D^§`-elements. -/
def pairSharp (x y : (Dsharp D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ P Q, x.mem P ∧ y.mem Q ∧ W = embPair P Q
  sub := by
    rintro W (rfl | ⟨P, Q, hP, hQ, rfl⟩)
    · exact MemS.gamma
    · exact MemS.pair (x.sub hP) (y.sub hQ)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) (rfl | ⟨P', Q', hP', hQ', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨P', Q', hP', hQ', by
        rw [Set.inter_eq_right.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP'))
          (memS_subset_gamma (y.sub hQ')))]⟩
    · exact Or.inr ⟨P, Q, hP, hQ, by
        rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP))
          (memS_subset_gamma (y.sub hQ)))]⟩
    · exact Or.inr ⟨P ∩ P', Q ∩ Q', x.inter_mem hP hP', y.inter_mem hQ hQ', by rw [embPair_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD (x.sub hP)) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        exact hcons (hsub ht).1
      | @pair P' Q' hP' hQ' =>
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact Or.inr ⟨P', Q', x.up_mem hP hP' hPP, y.up_mem hQ hQ' hQQ, rfl⟩

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- `toS ∘ fromS = id`. -/
theorem toS_fromS (s : (sumSys D hD).Element) : toS D hD (fromS D hD s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromS_mem_embZero D hD hX).mp hs
    · exact (fromS_mem_embPair D hD hP hQ).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromS_mem_embZero D hD hX).mpr hW⟩)
    · obtain ⟨P, Q, hP, hQ, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (fromS_mem_embPair D hD hP hQ).mpr hW⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- **Example 6.1 (Scott 1981, PRG-19) — the domain equation, as an order-isomorphism.**
`|D^§| ≃o |D + (D^§ × D^§)|`. -/
def dsharpEquiv : (Dsharp D hD).Element ≃o (sumSys D hD).Element where
  toFun := toS D hD
  invFun := fromS D hD
  left_inv := fromS_toS D hD
  right_inv := toS_fromS D hD
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h X hX
      cases z.sub hX with
      | gamma => exact z'.master_mem
      | @zero A hA =>
        exact (toS_mem_inj₀ D hD hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      | @pair P Q hP hQ =>
        exact (toS_mem_inj₁ D hD hP hQ).mp (h _ (Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, h _ hzPQ⟩)

end Equation

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}


section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD


/-- **Example 6.1 (Scott 1981, PRG-19) — the domain equation `D^§ ≅ D + (D^§ × D^§)`.** The tree
algebra `D^§` is, as a domain, isomorphic to `D + (D^§ × D^§)` — Scott's defining isomorphism, "as can
be seen by reference to the equation for `D^§` and the definitions of `+` and `×`". -/
theorem dsharp_domain_equation :
    Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD) :=
  ⟨dsharpEquiv D hD⟩


/-- **Example 6.1 (Scott 1981, PRG-19).** `λx. x^§` is an *isomorphic injection*: `x^§ ⊑ x'^§ ↔ x ⊑ x'`
(in particular one-one). -/
theorem inSharp_le_iff {x x' : D.Element} : inSharp D hD x ≤ inSharp D hD x' ↔ x ≤ x' := by
  constructor
  · intro h X hX
    rcases h (embZero X) (Or.inr ⟨X, hX, rfl⟩) with h0 | ⟨X', hX', heq⟩
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rw [← embZero_injective heq] at hX'; exact hX'
  · intro h W hW
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h _ hX, rfl⟩


/-- **Example 6.1 (Scott 1981, PRG-19).** `λx, y. ⟨x, y⟩` is an *isomorphic injection*:
`⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pairSharp_le_iff {x x' y y' : (Dsharp D hD).Element} :
    pairSharp D hD x y ≤ pairSharp D hD x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
    · rcases h (embPair P (Gamma D)) (Or.inr ⟨P, Gamma D, hP, y.master_mem, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD P (Gamma D))
      · obtain ⟨hPP, -⟩ := embPair_injective heq; rw [← hPP] at hP'; exact hP'
    · rcases h (embPair (Gamma D) Q) (Or.inr ⟨Gamma D, Q, x.master_mem, hQ, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD (Gamma D) Q)
      · obtain ⟨-, hQQ⟩ := embPair_injective heq; rw [← hQQ] at hQ'; exact hQ'
  · rintro ⟨hx, hy⟩ W hW
    rcases hW with rfl | ⟨P, Q, hP, hQ, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q, hx _ hP, hy _ hQ, rfl⟩

end Equation

end Example61
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

/-- The **union subdomain** of a directed family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are those lying in *some* member of `ℱ`. Directedness is what makes this closed
under consistent intersection. -/
def unionSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    NeighborhoodSystem α where
  mem X := ∃ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := by
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact ⟨𝒮, h𝒮, subFam_master_mem E (hℱ h𝒮)⟩
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮z, h𝒮z, hZz⟩ := hZ
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    have hXs : X ∈ 𝒮s := hxs hXx
    have hYs : Y ∈ 𝒮s := hys hYy
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮s) hXs
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮s) hYs
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮z) hZz
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) hXs hYs (E.inter_mem hEX hEY hEZ hsub)⟩
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) hX𝒮)
end

section
variable {α : Type*}

/-- The neighbourhood-set of the union subdomain is exactly `⋃₀ ℱ`. -/
theorem unionSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    {X | (unionSys E ℱ hne hℱ hdir).mem X} = ⋃₀ ℱ := by
  ext X
  exact Set.mem_sUnion.symm
end

section
variable {α : Type*}

/-- The union subdomain is a subsystem of `E` (Scott's remark: the directed union of subdomains is
again a subdomain). -/
theorem unionSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    unionSys E ℱ hne hℱ hdir ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact subFam_mem_E E (hℱ h𝒮) hX𝒮
  inter_closed := by
    intro X Y hX hY hEXY
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) (hxs hXx) (hys hYy) hEXY⟩
end

section
variable {α : Type*}

/-- **Closure under directed union** (Exercise 2.22's hypothesis (ii)) — Scott's remark. -/
theorem subFam_sUnion_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    ⋃₀ ℱ ∈ subFam E :=
  ⟨unionSys E ℱ hne hℱ hdir, unionSys_subsystem E ℱ hne hℱ hdir,
    (unionSys_nbset E ℱ hne hℱ hdir).symm⟩
end

section
variable {α : Type*}

/- concordance: source L3817 PROPOSITION 6.11 lattice of subsystems -/
/-- **Proposition 6.11 (Scott 1981, PRG-19).** For a neighbourhood system `E`, the set of
subsystems `{D ∣ D ◁ E}`, ordered by the subdomain relation `◁`, *forms a domain in its own
right*: it is order-isomorphic to the domain `|reprSystem (subFam E) …|` produced by the abstract
representation theorem (Exercise 2.22), using that `subFam E` is closed under non-empty
intersections (`subFam_sInter_mem`) and directed unions (Scott's remark, `subFam_sUnion_mem`). -/
def subsystemReprIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element :=
  (subIso E).trans
    (reprIso (subFam E) (subFam_sInter_mem E) (subFam_nonempty E) (subFam_sUnion_mem E)).symm
end

end DomainTheory.NeighbourhoodSystems.Proposition611
end
