module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.BinTree

abbrev Token := Fin 7

/-- Encoding: `0 ↦ Λ`, `1 ↦ 0`, `2 ↦ 1`, `3 ↦ 00`, `4 ↦ 01`, `5 ↦ 10`, `6 ↦ 11`. -/
def leaf00 : Set Token := {3}
def leaf01 : Set Token := {4}
def leaf10 : Set Token := {5}
def leaf11 : Set Token := {6}
def left : Set Token := {1, 3, 4}
def right : Set Token := {2, 5, 6}
def master : Set Token := Set.univ

def mem (X : Set Token) : Prop :=
  X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11

theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨
      X = leaf11 :=
  Iff.rfl

theorem mem_master : mem master := Or.inl rfl
theorem mem_left : mem left := Or.inr (Or.inl rfl)
theorem mem_right : mem right := Or.inr (Or.inr (Or.inl rfl))
theorem mem_leaf00 : mem leaf00 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem mem_leaf01 : mem leaf01 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem mem_leaf10 : mem leaf10 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
theorem mem_leaf11 : mem leaf11 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h | h | h | h | h
  · rw [master] at h; exact Set.empty_ne_univ h
  · have h1 : (1 : Token) ∈ left := by simp [left]
    rw [← h] at h1; cases h1
  · have h1 : (2 : Token) ∈ right := by simp [right]
    rw [← h] at h1; cases h1
  · have h1 : (3 : Token) ∈ leaf00 := by simp [leaf00]
    rw [← h] at h1; cases h1
  · have h1 : (4 : Token) ∈ leaf01 := by simp [leaf01]
    rw [← h] at h1; cases h1
  · have h1 : (5 : Token) ∈ leaf10 := by simp [leaf10]
    rw [← h] at h1; cases h1
  · have h1 : (6 : Token) ∈ leaf11 := by simp [leaf11]
    rw [← h] at h1; cases h1

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]
theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]
theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]
theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]
theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]
theorem left_inter_leaf11 : left ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf11]
theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]
theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]
theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]
theorem leaf11_inter_left : leaf11 ∩ left = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf11]
theorem right_inter_leaf00 : right ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf00]
theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]
theorem right_inter_leaf10 : right ∩ leaf10 = leaf10 := by
  ext t; fin_cases t <;> simp [right, leaf10]
theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]
theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf00]
theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]
theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  ext t; fin_cases t <;> simp [right, leaf10]
theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]
theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]
theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]
theorem leaf00_inter_leaf11 : leaf00 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf11]
theorem leaf01_inter_leaf00 : leaf01 ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]
theorem leaf01_inter_leaf10 : leaf01 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf10]
theorem leaf01_inter_leaf11 : leaf01 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf11]
theorem leaf10_inter_leaf00 : leaf10 ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]
theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf10]
theorem leaf10_inter_leaf11 : leaf10 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf10, leaf11]
theorem leaf11_inter_leaf00 : leaf11 ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf11]
theorem leaf11_inter_leaf01 : leaf11 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf11]
theorem leaf11_inter_leaf10 : leaf11 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf10, leaf11]

/-- Pairwise intersections of neighbourhoods are again neighbourhoods or empty. -/
theorem inter_mem_or_empty (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    mem (X ∩ Y) ∨ X ∩ Y = (∅ : Set Token) := by
  unfold mem at hX hY ⊢
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (master_inter _))
  · exact Or.inl (Or.inr (Or.inl (master_inter _)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (master_inter _))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (master_inter _)))))))
  · exact Or.inl (Or.inr (Or.inl (inter_master _)))
  · exact Or.inl (Or.inr (Or.inl (Set.inter_self _)))
  · exact Or.inr left_inter_right
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl left_inter_leaf00))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl left_inter_leaf01)))))
  · exact Or.inr left_inter_leaf10
  · exact Or.inr left_inter_leaf11
  · exact Or.inl (Or.inr (Or.inr (Or.inl (inter_master _))))
  · exact Or.inr right_inter_left
  · exact Or.inl (Or.inr (Or.inr (Or.inl (Set.inter_self _))))
  · exact Or.inr right_inter_leaf00
  · exact Or.inr right_inter_leaf01
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl right_inter_leaf10))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr right_inter_leaf11))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl leaf00_inter_left))))
  · exact Or.inr leaf00_inter_right
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _)))))
  · exact Or.inr leaf00_inter_leaf01
  · exact Or.inr leaf00_inter_leaf10
  · exact Or.inr leaf00_inter_leaf11
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl leaf01_inter_left)))))
  · exact Or.inr leaf01_inter_right
  · exact Or.inr leaf01_inter_leaf00
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _))))))
  · exact Or.inr leaf01_inter_leaf10
  · exact Or.inr leaf01_inter_leaf11
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _)))))))
  · exact Or.inr leaf10_inter_left
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl leaf10_inter_right))))))
  · exact Or.inr leaf10_inter_leaf00
  · exact Or.inr leaf10_inter_leaf01
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _)))))))
  · exact Or.inr leaf10_inter_leaf11
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inter_master _)))))))
  · exact Or.inr leaf11_inter_left
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr leaf11_inter_right))))))
  · exact Or.inr leaf11_inter_leaf00
  · exact Or.inr leaf11_inter_leaf01
  · exact Or.inr leaf11_inter_leaf10
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Set.inter_self _)))))))

def neighborhoodSystem : NeighborhoodSystem Token where
  mem
  master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_mem_or_empty X Y hX hY with h | h
    · exact h
    · rw [h] at hZsub
      have : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst this
      exact absurd hZ not_mem_empty

end DomainTheory.NeighbourhoodSystems.BinTree
