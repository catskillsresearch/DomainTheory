
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.4.** Products of retracts are retracts. -/
theorem tensorR_isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (tensorR a b) := by
  constructor
  change tensorR a b =
    graph (fun u => funOf (tensorR a b) (funOf (tensorR a b) u))
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one,
    retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
