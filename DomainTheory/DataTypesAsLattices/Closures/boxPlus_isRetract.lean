module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 (sum half), idempotence.** -/
theorem boxPlus_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxPlus a b) := by
  change boxPlus a b =
    graph (fun u => funOf (boxPlus a b) (funOf (boxPlus a b) u))
  apply graph_ext
  intro u
  rw [boxPlus_app_app ha hb u, boxPlus_app]

end DomainTheory.DataTypesAsLattices
