/-ai
The optimal fixed point of a nonempty set of fixed points lies below the infimum of the set.

The monotone construction places its result below the pre-fixed point to which it is applied, and that pre-fixed point is the infimum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.Basic

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_le
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `optimalFix S ⊑ ⋂S`. -/
theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
