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

inductive MemS (D : NeighborhoodSystem α) : Set (List Bool × α) → Prop
  | gamma : MemS D (Gamma D)
  | zero {X : Set α} : D.mem X → MemS D (embZero X)
  | pair {P Q : Set (List Bool × α)} : MemS D P → MemS D Q → MemS D (embPair P Q)

end Example61
end

section
open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

def embBit (b : Bool) (X : Set Str) : Set Str := {w | ∃ w', w = b :: w' ∧ w' ∈ X}

@[simp] theorem mem_embBit {b : Bool} {X : Set Str} {w : Str} :
    w ∈ embBit b X ↔ ∃ w', w = b :: w' ∧ w' ∈ X := Iff.rfl

theorem B_nonempty : ∀ X, B.mem X → X.Nonempty := by
  rintro X ⟨σ, rfl⟩; exact ⟨σ, List.prefix_rfl⟩

abbrev BB : NeighborhoodSystem (Option (Str ⊕ Str)) := sum B B B_nonempty B_nonempty

theorem embBit_eq_prepend (b : Bool) (X : Set Str) : embBit b X = prepend [b] X := by
  ext w
  simp only [mem_embBit, mem_prepend]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨τ, hX, rfl⟩; exact ⟨τ, rfl, hX⟩

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
