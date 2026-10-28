module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_18 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    typed (comp sndC (tensorR a b)) (arrowR (tensorR a b) b) := by
  change comp sndC (tensorR a b) =
    funOf (arrowR (tensorR a b) b) (comp sndC (tensorR a b))
  rw [arrowR.app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp.app, sndC.app, retract_app hab]
  rw [tensorR_app, pairSeq_app_one, retract_app hb]

end DomainTheory.DataTypesAsLattices
