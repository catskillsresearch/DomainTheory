module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_12 (a b a' b' : Pomega) :
    comp (tensorR a b) (tensorR a' b') = tensorR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [tensorR.app, tensorR.app, PairSeq.app_zero, PairSeq.app_one]
  simp only [comp.app]

end DomainTheory.DataTypesAsLattices
