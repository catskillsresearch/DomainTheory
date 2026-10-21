/-ai
Scott 1976, (4.37). If a is a retract, then a composed with elimination composed with the sum of a with itself is typed as an arrow from that sum to a.

Typedness unfolds to the arrow equation, which rewrites by the arrow rule. Graph extensionality and composition are followed by the retract equation of the sum of a with itself and the retract equation of a.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.37).** `a ∘ out ∘ (a ⊕ a) : (a ⊕ a) ∘→ a`. -/
theorem eq_4_37 {a : Pomega} (ha : IsRetract a) :
    typed (comp a (comp outC (plusR a a))) (arrowR (plusR a a) a) := by
  change comp a (comp outC (plusR a a)) =
    funOf (arrowR (plusR a a) a) (comp a (comp outC (plusR a a)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha ha), retract_app ha]

end DomainTheory.DataTypesAsLattices
