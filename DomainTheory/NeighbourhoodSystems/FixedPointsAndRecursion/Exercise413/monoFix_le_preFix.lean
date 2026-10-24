module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.preFix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.mem_preFix

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.sInf_le
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `monoFix f ha ⊑ x` for every pre-fixed point `x` (`f(x) ⊑ x`). -/
theorem monoFix_le_preFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {x : V.Element} (hx : f x ≤ x) : monoFix f ha ≤ x :=
  V.sInf_le (preFix f) ⟨a, ha⟩ hx

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
