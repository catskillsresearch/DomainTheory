
module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.5 (i).** `a ⊕ b` is a retract when `a` and `b` are. -/
theorem plusR_isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (plusR a b) := by
  constructor
  change plusR a b =
    graph (fun u => funOf (plusR a b) (funOf (plusR a b) u))
  apply graph_ext
  intro u
  rw [plusR_app.app a b u]
  rcases dcondSet.cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, plusR_app.app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet.ofNat_zero, retract_app ha]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, plusR_app.app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet.ofNat_one, retract_app hb]
  · rw [dcondSet.of_mixed h.1 h.2, plusR_app.top]
  · rw [dcondSet.of_empty h.1 h.2, plusR_app.bot]

end DomainTheory.DataTypesAsLattices
