module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems

def NeighborhoodSystem.IsPositive {α : Type*} (V : NeighborhoodSystem α) : Prop :=
  ∀ ⦃X Y : Set α⦄, V.mem X → V.mem Y → (V.mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)

def NeighborhoodSystem.DiffClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → X \ Y = ∅ ∨ D.mem (X \ Y)

def NeighborhoodSystem.NoMinimal {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X : Set α}, D.mem X →
    ∃ Y Z : Set α, D.mem Y ∧ D.mem Z ∧ Y.Nonempty ∧ Z.Nonempty ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X

def NestedOrDisjoint {α : Type*} (mem : Set α → Prop) : Prop :=
  ∀ ⦃X Y : Set α⦄, mem X → mem Y → X ⊆ Y ∨ Y ⊆ X ∨ X ∩ Y = ∅

def NeighborhoodSystem.ofPositive {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    NeighborhoodSystem α where
  mem
  master
  master_nonempty
  master_mem
  sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hZZ : mem (Z ∩ Z) := by rwa [Set.inter_self]
    have hZne : (Z ∩ Z).Nonempty := (pos hZ hZ).mp hZZ
    rw [Set.inter_self] at hZne
    exact (pos hX hY).mpr (hZne.mono hZsub)

end DomainTheory.NeighbourhoodSystems
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

abbrev Tok := Fin 3

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def a : Set Tok := {0, 1}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def b : Set Tok := {1, 2}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def master : Set Tok := Set.univ

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def memSet : Set (Set Tok) := {master, a, b}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def mem (X : Set Tok) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem inter_eq (X Y : Set Tok) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = a ∨ X ∩ Y = b ∨ X ∩ Y = ({1} : Set Tok) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inl (by ext x; fin_cases x <;> simp [master, a, b])
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_b : mem b := (mem_iff _).mpr (Or.inr (Or.inr rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_master : mem master := (mem_iff _).mpr (Or.inl rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem not_mem_sub_one {Z : Set Tok} (hZ : mem Z) (hsub : Z ⊆ ({1} : Set Tok)) : False := by
  rcases (mem_iff Z).mp hZ with rfl | rfl | rfl
  · exact absurd (hsub (show (0 : Tok) ∈ master by simp [master])) (by simp)
  · exact absurd (hsub (show (0 : Tok) ∈ a by simp [a])) (by simp)
  · exact absurd (hsub (show (2 : Tok) ∈ b by simp [b])) (by simp)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def notPositiveSystem : NeighborhoodSystem Tok where
  mem
  master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_a
    · rw [h]; exact mem_b
    · rw [h] at hZsub; exact (not_mem_sub_one hZ hZsub).elim

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

def positiveExample : NeighborhoodSystem (Fin 2) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩)
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩) (by intro X _; exact Set.subset_univ X)
    (by intro X Y _ _; exact Iff.rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by ext x; fin_cases x <;> simp [a, b]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

namespace DomainTheory.NeighbourhoodSystems.Exercise119

set_option linter.unusedVariables false

theorem example_119 : Not
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive DomainTheory.NeighbourhoodSystems.Exercise119.Tok
    DomainTheory.NeighbourhoodSystems.Exercise119.notPositiveSystem) :=
  DomainTheory.NeighbourhoodSystems.Exercise119.not_isPositive

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise119
end
