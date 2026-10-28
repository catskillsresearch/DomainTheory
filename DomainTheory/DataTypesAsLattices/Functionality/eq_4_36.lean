module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_bool_idem
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_fst
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_36 (a b : Pomega) :
    typed (comp whichC (plusR a b)) (arrowR (plusR a b) boolR) := by
  change comp whichC (plusR a b) =
    funOf (arrowR (plusR a b) boolR) (comp whichC (plusR a b))
  rw [arrowR.app]
  apply graph_ext
  intro u
  simp only [comp.app, whichC, fstC.app]
  rw [plusR_fst, boolR.app, plusR_fst, plusR_fst, dcondSet_bool_idem, dcondSet_bool_idem]

end DomainTheory.DataTypesAsLattices
