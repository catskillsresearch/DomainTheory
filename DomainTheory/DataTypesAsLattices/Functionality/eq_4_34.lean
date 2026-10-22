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
