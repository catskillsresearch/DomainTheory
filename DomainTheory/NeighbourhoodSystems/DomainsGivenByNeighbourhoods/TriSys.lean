module

import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.PositiveDiff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more

public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.IntervalCases
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.TriSys
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def A : Set (Fin 3) := {0, 1}

def B : Set (Fin 3) := {1, 2}

def Cc : Set (Fin 3) := {0, 2}

def family : Set (Set (Fin 3)) := {A, B, Cc}

def system : NeighborhoodSystem (Fin 3) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (⟨0, Set.mem_univ 0⟩) (⟨0, Set.mem_univ 0⟩)
    (fun {_} _ => Set.subset_univ _) (fun _ _ _ _ => Iff.rfl)

theorem system_master : system.master = (Set.univ : Set (Fin 3)) := rfl

def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A]⟩
  · exact ⟨1, by simp [A, B]⟩
  · exact ⟨0, by simp [A, Cc]⟩
  · exact ⟨1, by simp [A, B]⟩
  · exact ⟨1, by simp [B]⟩
  · exact ⟨2, by simp [B, Cc]⟩
  · exact ⟨0, by simp [A, Cc]⟩
  · exact ⟨2, by simp [B, Cc]⟩
  · exact ⟨0, by simp [Cc]⟩

theorem triple_interUpTo_empty : system.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo.succ, NeighborhoodSystem.interUpTo.zero, system_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

theorem triple_mem : ∀ i, i < 3 → triple i ∈ family := by
  intro i hi
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem not_finitelyConsistent : ¬ system.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  rw [hZsub] at hZne
  exact Set.not_nonempty_empty hZne

end DomainTheory.NeighbourhoodSystems.TriSys
