module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.PairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_13 (a b a' b' : Pomega) :
    comp (plusR a b) (plusR a' b') = plusR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [plusR.app a' b' u]
  rcases dcondSet.cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, plusR.app,
      PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_zero,
      dcondSet.of_zero_not_pos h.1 h.2]
    simp only [comp.app]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, plusR.app,
      PairSeq.app_zero, PairSeq.app_one, dcondSet.ofNat_one,
      dcondSet.of_pos_not_zero h.1 h.2]
    simp only [comp.app]
  · rw [dcondSet.of_mixed h.1 h.2, plusR.top, dcondSet.of_mixed h.1 h.2]
  · rw [dcondSet.of_empty h.1 h.2, plusR.bot, dcondSet.of_empty h.1 h.2]

end DomainTheory.DataTypesAsLattices
