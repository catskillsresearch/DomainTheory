module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.coe_stepFin

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


theorem coe_foldl_stepFin (e : SExpr) (w : List Bool) (S : Finset (autState e)) :
    (↑(w.foldl (stepFin e) S) : Set (autState e)) = (toNFA e).evalFrom ↑S w := by
  induction w generalizing S with
  | nil => rfl
  | cons c w ih =>
    show (↑(w.foldl (stepFin e) (stepFin e S c)) : Set (autState e)) = _
    rw [ih (stepFin e S c), NFA.evalFrom_cons, coe_stepFin e S c]

end Exercise722
end DomainTheory.NeighbourhoodSystems
