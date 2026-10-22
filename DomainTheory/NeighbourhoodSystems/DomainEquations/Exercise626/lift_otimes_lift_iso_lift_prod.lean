module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}


variable {hD : ∀ X, D.mem X → X.Nonempty}


variable {A B C : ScottSys}


variable {D E : ScottSys}


/-- **Exercise 6.26 — `𝒟_⊥ ⊗ ℰ_⊥ ≅ (𝒟 × ℰ)_⊥`** (the answer to Scott's `??`). The smash product of
two lifts is the lift of the product. -/
theorem lift_otimes_lift_iso_lift_prod :
    (D.lift.otimes E.lift).sys ≅ᴰ (D.prod E).lift.sys := ⟨liftProdEquiv⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
