module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.b
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_iff

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Classification of binary intersections in `𝒟`. -/
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
