/-ai
Every element of Example 1.3 is the bottom filter, the intermediate filter, or the total filter.

If the element contains {2}, it is the total filter. If it contains {1, 2} but not {2}, it is the intermediate filter. Otherwise the two filters contain the same neighbourhoods: every neighbourhood is the master, {1, 2}, or {2}, the last two are excluded, and the master belongs to every element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


/-- Every element of Example 1.3 is one of the three filters in the linear chain. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemTwelve ∨ x = elemTwo := by
  by_cases htwo : x.mem two
  · exact Or.inr (Or.inr (mem_two_of_mem x htwo))
  by_cases htwelve : x.mem twelve
  · exact Or.inr (Or.inl (mem_twelve_of_mem x htwelve htwo))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | htwelve' | htwo'
    · rfl
    · exact absurd (htwelve' ▸ hx) htwelve
    · exact absurd (htwo' ▸ hx) htwo
  · intro hx
    rw [hx]
    exact x.master_mem

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
