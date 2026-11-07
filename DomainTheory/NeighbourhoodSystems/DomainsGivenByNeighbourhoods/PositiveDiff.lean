module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.PositiveDiff

open DomainTheory.NeighbourhoodSystems

abbrev Tok := Fin 3


def a : Set Tok := {0, 1}


def b : Set Tok := {1, 2}


def master : Set Tok := Set.univ


def memSet : Set (Set Tok) := {master, a, b}


def mem (X : Set Tok) : Prop := X ∈ memSet


theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]


theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by
  ext x
  fin_cases x
  · simp [a, b]
  · simp [a, b]
  · simp [a, b]

theorem inter_eq (X Y : Set Tok) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = a ∨ X ∩ Y = b ∨ X ∩ Y = ({1} : Set Tok) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inl (Set.inter_self _)
    · exact Or.inr (Or.inl (by rw [master, Set.univ_inter]))
    · exact Or.inr (Or.inr (Or.inl (by rw [master, Set.univ_inter])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by rw [master, Set.inter_univ]))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr (Or.inr a_inter_b))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by rw [master, Set.inter_univ])))
    · exact Or.inr (Or.inr (Or.inr (by rw [Set.inter_comm, a_inter_b])))
    · exact Or.inr (Or.inr (Or.inl (Set.inter_self _)))


theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))


theorem mem_b : mem b := (mem_iff _).mpr (Or.inr (Or.inr rfl))


theorem mem_master : mem master := (mem_iff _).mpr (Or.inl rfl)


theorem not_mem_sub_one {Z : Set Tok} (hZ : mem Z) (hsub : Z ⊆ ({1} : Set Tok)) : False := by
  rcases (mem_iff Z).mp hZ with rfl | rfl | rfl
  · exact absurd (hsub (show (0 : Tok) ∈ master by simp [master])) (by simp)
  · exact absurd (hsub (show (0 : Tok) ∈ a by simp [a])) (by simp)
  · exact absurd (hsub (show (2 : Tok) ∈ b by simp [b])) (by simp)


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


def positiveExample : NeighborhoodSystem (Fin 2) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩)
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩) (by intro X _; exact Set.subset_univ X)
    (by intro X Y _ _; exact Iff.rfl)


theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2


theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)

theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl

end DomainTheory.NeighbourhoodSystems.PositiveDiff
