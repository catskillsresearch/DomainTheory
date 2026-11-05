module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Example13

abbrev Token := Fin 3

def master : Set Token := Set.univ

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

def twelve : Set Token := (insert 2 {1} : Set Token)

def two : Set Token := {2}

def memSet : Set (Set Token) := {master, twelve, two}

def mem (X : Set Token) : Prop := X ∈ memSet

theorem mem_master : mem master := by simp [mem, memSet, master, twelve, two]

theorem mem_twelve : mem twelve := by simp [mem, memSet, master, twelve, two]

theorem mem_two : mem two := by simp [mem, memSet, master, twelve, two]

theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = twelve ∨ X = two := by
  constructor
  · intro h
    simp [mem, memSet, master, twelve, two] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two

theorem twelve_inter_two : twelve ∩ two = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

theorem two_inter_twelve : two ∩ twelve = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

theorem inter_eq (X Y : Set Token) (h : mem X) (h' : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = twelve ∨ X ∩ Y = two := by
  rcases (mem_iff X).mp h with rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp h' with rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (master_inter _))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (twelve_inter_two))
  · exact Or.inr (Or.inr (inter_master _))
  · exact Or.inr (Or.inr (two_inter_twelve))
  · exact Or.inr (Or.inr (Set.inter_self _))

def neighborhoodSystem : NeighborhoodSystem Token where
  mem
  master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_twelve
    · rw [h]; exact mem_two

/-- **Example 1.3.** Tokens `Δ = {0, 1, 2}` and neighbourhoods
`𝒟 = {{0, 1, 2}, {1, 2}, {2}}` form a neighbourhood system. -/
theorem example_1_3 :
    ∃ (V : NeighborhoodSystem Token),
      V.master = (Set.univ : Set Token) ∧
        (∀ X : Set Token,
          V.mem X ↔
            X = Set.univ ∨ X = ({1, 2} : Set Token) ∨ X = ({2} : Set Token)) :=
  ⟨neighborhoodSystem, rfl, fun X => by
    have h12 : twelve = ({1, 2} : Set Token) := by
      ext t; fin_cases t <;> simp [twelve]
    refine (mem_iff X).trans ?_
    simp [master, two, h12]⟩

end DomainTheory.NeighbourhoodSystems.Example13
end
