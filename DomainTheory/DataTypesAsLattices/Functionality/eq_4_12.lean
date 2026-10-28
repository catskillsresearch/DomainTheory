module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_12 (a b a' b' : Pomega) :
    comp (tensorR a b) (tensorR a' b') = tensorR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  simp only [comp.app]

end DomainTheory.DataTypesAsLattices
