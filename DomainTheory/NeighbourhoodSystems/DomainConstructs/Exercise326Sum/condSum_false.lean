module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSumEmb
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_zeroset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_oneset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_left
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_masterC
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSumEmb_toElementMap

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- **Exercise 3.26.** `condSum(false, x, y) = in₁(y)`. -/
theorem condSum_false (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.falseElt (pair x y))
      = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_false]

end DomainTheory.NeighbourhoodSystems.Exercise326
