/-ai
The image of a function-space element x under the product of d lies in Y if and only if Y is a neighbourhood and some neighbourhood X lies in x, is contained in Y, and is self-related by the product.

Rewrite by the membership reduction to the closed form. From a neighbourhood and a membership of the closed form, the hard direction supplies X. Conversely, the easy direction gives membership of the image, and the same reduction turns that membership back into the neighbourhood and the closed-form membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.hii_hard_direction

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27(b)(3), in full: `piD d` satisfies Scott's step-closure formula (ii), for *any*
`d` at all** (`d`'s polymorphism is not needed). Combines the reduction (b)(3)(a) with the easy
(`hii_easy_direction`) and now-closed hard (`hii_hard_direction`) halves. -/
theorem hii_piD (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  rw [piD_toElementMap_mem_iff]
  constructor
  · rintro ⟨hYE, hmem⟩
    exact ⟨hYE, hii_hard_direction d x hYE hmem⟩
  · rintro ⟨hYE, X, hXx, hXY, hXX⟩
    have := hii_easy_direction d x hYE hXx hXY hXX
    rwa [piD_toElementMap_mem_iff] at this

end DomainTheory.NeighbourhoodSystems
