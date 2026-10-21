/-ai
The optimal fixed point of a nonempty set of fixed points is a fixed point.

It is obtained from the monotone construction, and that construction produces a fixed point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `optimalFix S` is a fixed point. -/
theorem optimalFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    f (optimalFix f hf S hS hfix) = optimalFix f hf S hS hfix :=
  monoFix_isFixed f hf _

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
