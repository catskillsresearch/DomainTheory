module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.CombC
public import DomainTheory.DataTypesAsLattices.Functionality.PairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_32 {a b : Pomega} (ha : Retract a) :
    typed (comp (plusR a b) (comp inleftC a)) (arrowR a (plusR a b)) := by
  change comp (plusR a b) (comp inleftC a) =
    funOf (arrowR a (plusR a b)) (comp (plusR a b) (comp inleftC a))
  rw [arrowR.app]
  apply graph_ext
  intro x
  simp only [comp.app, inleftC.app, retract_app ha]
  rw [plusR.app, plusR.app, PairSeq.app_zero, PairSeq.app_one,
    dcondSet.ofNat_zero, retract_app ha]
  rw [PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_zero, retract_app ha]

end DomainTheory.DataTypesAsLattices
