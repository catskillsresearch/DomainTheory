module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.gfpSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem example_414 :
    (∀ {A : Type*} (f : Set A → Set A) {y : Set A}, f y = y → y ⊆ gfpSet f) ∧
    (∀ {A : Type*} (f : Set A → Set A), Monotone f → f (gfpSet f) = gfpSet f) :=
  ⟨@gfpSet_greatest, @gfpSet_isFixed⟩

end DomainTheory.NeighbourhoodSystems
