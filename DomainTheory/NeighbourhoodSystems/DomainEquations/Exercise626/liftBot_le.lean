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


/-- `liftBot` is the least element of `𝒟_⊥`. -/
theorem liftBot_le (z : (liftTok D hD).Element) : liftBot D hD ≤ z := by
  rintro W rfl; exact z.master_mem

end Exercise619
end DomainTheory.NeighbourhoodSystems
