module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_21 (f f' : Pomega) :
    comp sndC (tensorR f f') = comp f' sndC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [sndC.app, tensorR_app, pairSeq_app_one, sndC.app]

end DomainTheory.DataTypesAsLattices
