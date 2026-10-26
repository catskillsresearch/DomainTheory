module

public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.outrightC
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.35).** `b ∘ outright ∘ (a ⊕ b) : (a ⊕ b) ∘→ b`. -/
theorem eq_4_35 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    typed (comp b (comp outrightC (plusR a b))) (arrowR (plusR a b) b) := by
  change comp b (comp outrightC (plusR a b)) =
    funOf (arrowR (plusR a b) b) (comp b (comp outrightC (plusR a b)))
  rw [arrowR.app]
  apply graph_ext
  intro u
  simp only [comp.app]
  rw [retract_app (plusR_isRetract ha hb), retract_app hb]

end DomainTheory.DataTypesAsLattices
