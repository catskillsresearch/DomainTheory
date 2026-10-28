module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_17 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    typed (comp fstC (tensorR a b)) (arrowR (tensorR a b) a) := by
  change comp fstC (tensorR a b) =
    funOf (arrowR (tensorR a b) a) (comp fstC (tensorR a b))
  rw [arrowR.app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp.app, fstC.app, retract_app hab]
  rw [tensorR_app, pairSeq_app_zero, retract_app ha]

end DomainTheory.DataTypesAsLattices
