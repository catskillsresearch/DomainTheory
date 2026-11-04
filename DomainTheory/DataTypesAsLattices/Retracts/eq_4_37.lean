module

public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.CombC
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_37 {a : Pomega} (ha : Retract a) :
    typed (comp a (comp outC (plusR a a))) (arrowR (plusR a a) a) := by
  change comp a (comp outC (plusR a a)) =
    funOf (arrowR (plusR a a) a) (comp a (comp outC (plusR a a)))
  rw [arrowR.app]
  apply graph_ext
  intro u
  simp only [comp.app]
  rw [retract_app (plusR.isRetract ha ha), retract_app ha]

end DomainTheory.DataTypesAsLattices
