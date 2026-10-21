/-ai
The function-space product of d relates a set X to itself if and only if X is a neighbourhood and the section of the uncurried product at X lies in X.

Rewrite by the general relation law for the product. One direction drops the repeated neighbourhood hypothesis, and the other restores it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.27(b)(2), specialized to self-relation** (the shape Theorem 8.5's formula (ii)
actually tests, `a.rel X X`): combines (a) and (b) into the single membership-test formula that
Exercise 8.27(b)(3) will chain through `subU`'s and each `D'_s`'s own formula (ii). -/
theorem piD_rel_self_iff (d : ApproximableMap U U) {X : Set (ApproximableMap U U)} :
    (piD d).rel X X ↔ ∃ hX : (funSpace U U).mem X, gSection (piDUncurried d) hX ∈ X := by
  rw [piD_rel_iff]
  exact ⟨fun ⟨hX, _, hmem⟩ => ⟨hX, hmem⟩, fun ⟨hX, hmem⟩ => ⟨hX, hX, hmem⟩⟩

end DomainTheory.NeighbourhoodSystems
