module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_le_preFix

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `monoFix f ha ⊑ a`: the least fixed point lies below the given pre-fixed point `a`. -/
theorem monoFix_le (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) :
    monoFix f ha ≤ a := monoFix_le_preFix f ha ha

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
