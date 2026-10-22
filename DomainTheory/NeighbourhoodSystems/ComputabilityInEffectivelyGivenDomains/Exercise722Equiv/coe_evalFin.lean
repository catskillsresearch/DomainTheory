module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.coe_startFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.coe_foldl_stepFin

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


theorem coe_evalFin (e : SExpr) (w : List Bool) :
    (↑(evalFin e w) : Set (autState e)) = (toNFA e).eval w := by
  show (↑(w.foldl (stepFin e) (startFin e)) : Set (autState e))
    = (toNFA e).evalFrom (toNFA e).start w
  rw [coe_foldl_stepFin e w (startFin e), coe_startFin e]

end Exercise722
end DomainTheory.NeighbourhoodSystems
