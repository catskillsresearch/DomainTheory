/-ai
Scott 1976, (4.34). If a and b are retracts, then a composed with left elimination composed with the sum of a and b is typed as an arrow from that sum to a.

Typedness unfolds to the arrow equation, which rewrites by the arrow rule. Graph extensionality and composition are followed by the retract equation of the sum and the retract equation of a.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.34).** `a ∘ outleft ∘ (a ⊕ b) : (a ⊕ b) ∘→ a`. -/
theorem eq_4_34 {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    typed (comp a (comp outleftC (plusR a b))) (arrowR (plusR a b) a) := by
  change comp a (comp outleftC (plusR a b)) =
    funOf (arrowR (plusR a b) a) (comp a (comp outleftC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app ha]

end DomainTheory.DataTypesAsLattices
