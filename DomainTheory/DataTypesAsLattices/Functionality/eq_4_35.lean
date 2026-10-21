/-ai
Scott 1976, (4.35). If a and b are retracts, then b composed with right elimination composed with the sum of a and b is typed as an arrow from that sum to b.

Typedness unfolds to the arrow equation, which rewrites by the arrow rule. Graph extensionality and composition are followed by the retract equation of the sum and the retract equation of b.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.35).** `b ∘ outright ∘ (a ⊕ b) : (a ⊕ b) ∘→ b`. -/
theorem eq_4_35 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp b (comp outrightC (plusR a b))) (arrowR (plusR a b) b) := by
  change comp b (comp outrightC (plusR a b)) =
    funOf (arrowR (plusR a b) b) (comp b (comp outrightC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app hb]

end DomainTheory.DataTypesAsLattices
