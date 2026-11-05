module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Example14

abbrev Token := Fin 7

def leaf00 : Set Token := {3}

def leaf01 : Set Token := {4}

theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]

theorem leaf01_inter_leaf00 : leaf01 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf01

def leaf10 : Set Token := {5}

theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]

theorem leaf01_inter_leaf10 : leaf01 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf10]

theorem leaf10_inter_leaf00 : leaf10 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf10

theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf10

def leaf11 : Set Token := {6}

theorem leaf00_inter_leaf11 : leaf00 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf11]

theorem leaf01_inter_leaf11 : leaf01 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf11]

theorem leaf10_inter_leaf11 : leaf10 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf10, leaf11]

theorem leaf11_inter_leaf00 : leaf11 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf11

theorem leaf11_inter_leaf01 : leaf11 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf11

theorem leaf11_inter_leaf10 : leaf11 ∩ leaf10 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf10_inter_leaf11

def left : Set Token := {1, 3, 4}

theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]

theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  rw [Set.inter_comm]; exact left_inter_leaf00

theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]

theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  rw [Set.inter_comm]; exact left_inter_leaf01

theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]

theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf10

theorem left_inter_leaf11 : left ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf11]

theorem leaf11_inter_left : leaf11 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf11

def master : Set Token := Set.univ

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

def right : Set Token := {2, 5, 6}

theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]

def memSet : Set (Set Token) := {master, left, right, leaf00, leaf01, leaf10, leaf11}

def mem (X : Set Token) : Prop := X ∈ memSet

theorem mem_leaf00 : mem leaf00 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_leaf01 : mem leaf01 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_leaf10 : mem leaf10 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_leaf11 : mem leaf11 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_left : mem left := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_master : mem master := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_right : mem right := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11 := by
  constructor
  · intro h
    simpa [mem, memSet] using h
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_right
    · exact mem_leaf00
    · exact mem_leaf01
    · exact mem_leaf10
    · exact mem_leaf11

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h | h | h | h | h
  · have : (0 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [master]
    simp at this
  · have : (1 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [left]
    simp at this
  · have : (2 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [right]
    simp at this
  · have : (3 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf00]
    simp at this
  · have : (4 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf01]
    simp at this
  · have : (5 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf10]
    simp at this
  · have : (6 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf11]
    simp at this

theorem right_inter_leaf00 : right ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf00]

theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf00

theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]

theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf01

theorem right_inter_leaf10 : right ∩ leaf10 = leaf10 := by
  ext t; fin_cases t <;> simp [right, leaf10]

theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10

theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]

theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  rw [Set.inter_comm]; exact right_inter_leaf11

theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_right

theorem inter_eq (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = left ∨ X ∩ Y = right ∨ X ∩ Y = leaf00 ∨
      X ∩ Y = leaf01 ∨ X ∩ Y = leaf10 ∨ X ∩ Y = leaf11 ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [master_inter, inter_master, Set.inter_self,
      left_inter_right, right_inter_left, left_inter_leaf10, leaf10_inter_left,
      left_inter_leaf11, leaf11_inter_left, right_inter_leaf00, leaf00_inter_right,
      right_inter_leaf01, leaf01_inter_right, leaf00_inter_leaf01, leaf01_inter_leaf00,
      leaf00_inter_leaf10, leaf10_inter_leaf00, leaf00_inter_leaf11, leaf11_inter_leaf00,
      leaf01_inter_leaf10, leaf10_inter_leaf01, leaf01_inter_leaf11, leaf11_inter_leaf01,
      leaf10_inter_leaf11, leaf11_inter_leaf10,
      left_inter_leaf00, leaf00_inter_left, left_inter_leaf01, leaf01_inter_left,
      right_inter_leaf10, leaf10_inter_right, right_inter_leaf11, leaf11_inter_right,
      true_or, or_true]

def neighborhoodSystem : NeighborhoodSystem Token where
  mem
  master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h | h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_left
    · rw [h]; exact mem_right
    · rw [h]; exact mem_leaf00
    · rw [h]; exact mem_leaf01
    · rw [h]; exact mem_leaf10
    · rw [h]; exact mem_leaf11
    · rw [h] at hZsub
      have hz : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst hz
      exact absurd hZ not_mem_empty

/-- **Example 1.4.** Tokens $\Delta=\{\Lambda,0,1,00,01,10,11\}$ and neighbourhoods
$\mathcal{D}=\{\Delta,\{0,00,01\},\{1,10,11\},\{00\},\{01\},\{10\},\{11\}\}$
form a neighbourhood system. -/
theorem example_1_4 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token,
          V.mem X ↔
            X = Set.univ ∨ X = left ∨ X = right ∨
              X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11) :=
  ⟨neighborhoodSystem, rfl, fun X => (mem_iff X).trans (by simp [master])⟩

end DomainTheory.NeighbourhoodSystems.Example14
end
