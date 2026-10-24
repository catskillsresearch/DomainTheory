module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_10

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_18
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
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

@[simp] theorem mem_embBit {b : Bool} {X : Set Str} {w : Str} :
    w ∈ embBit b X ↔ ∃ w', w = b :: w' ∧ w' ∈ X := Iff.rfl

/-- Scott's standing assumption `∅ ∉ B`: every neighbourhood of `B` is nonempty (cones contain their
generating prefix). -/
theorem B_nonempty : ∀ X, B.mem X → X.Nonempty := by
  rintro X ⟨σ, rfl⟩; exact ⟨σ, List.prefix_rfl⟩

/-- The right-hand side of Scott's domain equation: the sum system `B + B` (Exercise 3.18). -/
abbrev BB : NeighborhoodSystem (Option (Str ⊕ Str)) := sum B B B_nonempty B_nonempty

/-- `bX = b·X` is exactly the single-bit prepend of Example 1.B. -/
theorem embBit_eq_prepend (b : Bool) (X : Set Str) : embBit b X = prepend [b] X := by
  ext w
  simp only [mem_embBit, mem_prepend]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨τ, hX, rfl⟩; exact ⟨τ, rfl, hX⟩

/-- `b(σΣ*) = (bσ)Σ*`: prepending a bit to a cone gives the cone of the longer prefix. -/
theorem embBit_cone (b : Bool) (σ : Str) : embBit b (cone σ) = cone (b :: σ) := by
  rw [embBit_eq_prepend, prepend_cone]; rfl

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

theorem embBit_inter_ne {b b' : Bool} (h : b ≠ b') (X Y : Set Str) :
    embBit b X ∩ embBit b' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq
  exact h heq.1

theorem embBit_ne {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty) :
    embBit b X ≠ embBit b' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (b :: w') ∈ embBit b' Y := heq ▸ (⟨w', rfl, hw'⟩ : (b :: w') ∈ embBit b X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he
  exact h he.1

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

theorem embBit_injective {b : Bool} {X X' : Set Str} (h : embBit b X = embBit b X') : X = X' :=
  Set.Subset.antisymm (embBit_subset.mp h.subset) (embBit_subset.mp h.symm.subset)

end Example62
end
end DomainTheory.NeighbourhoodSystems
end
