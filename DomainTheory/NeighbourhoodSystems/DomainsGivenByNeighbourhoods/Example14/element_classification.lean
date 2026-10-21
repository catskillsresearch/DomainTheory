/-ai
Every element of Example 1.4 is the bottom element, the partial element at node 0, the partial element at node 1, or one of the four total leaf elements.

If the element contains the leaf 00, 01, 10, or 11, the corresponding recognition lemma identifies it. If it contains none of those leaves but contains the left branch, it is the partial element at node 0, and if it contains the right branch, it is the partial element at node 1. Otherwise extensionality shows that its only neighbourhood is the master neighbourhood: every neighbourhood of the element is one of the seven, the six proper neighbourhoods are excluded by the case hypotheses, and the master neighbourhood belongs by the master axiom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


/-- **Example 1.4 classification.** Every filter is one of the seven: the bottom `⊥`, the two
branch partials `elemZero`/`elemOne`, or one of the four total leaf elements. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne ∨ x = elem00 ∨ x = elem01 ∨ x = elem10 ∨ x = elem11 := by
  by_cases h00 : x.mem leaf00
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf00_imp x h00))))
  by_cases h01 : x.mem leaf01
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf01_imp x h01)))))
  by_cases h10 : x.mem leaf10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf10_imp x h10))))))
  by_cases h11 : x.mem leaf11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_leaf11_imp x h11))))))
  by_cases hl : x.mem left
  · exact Or.inr (Or.inl (mem_left_imp x hl h00 h01))
  by_cases hr : x.mem right
  · exact Or.inr (Or.inr (Or.inl (mem_right_imp x hr h10 h11)))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hx hl
    · exact absurd hx hr
    · exact absurd hx h00
    · exact absurd hx h01
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rw [hx]
    exact x.master_mem

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
