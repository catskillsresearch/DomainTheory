/-ai
The optimal fixed point of a nonempty set of fixed points of a monotone endomap is the least fixed point, given by the monotone construction, of the pre-fixed point obtained as the infimum of the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise416.f_sInf_le

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.16 (Scott 1981, PRG-19).** The *optimal* fixed point associated with a non-empty
set `S` of fixed points: the least fixed point sitting below `⋂S` (Exercise 4.13(1) applied to the
pre-fixed point `⋂S`). -/
def optimalFix (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
    (hfix : ∀ s ∈ S, f s = s) : V.Element :=
  monoFix f (f_sInf_le f hf S hS hfix)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
