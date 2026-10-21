/-ai
Scott 1976, (4.32). If a is a retract, then the sum of a and b, composed with left injection composed with a, is typed as an arrow from a to that sum.

Typedness unfolds to the arrow equation, which rewrites by the arrow rule. Graph extensionality and simplification by composition, the left-injection rule, and the retract equation of a are followed by two sum rules, the pair projections, the zero rule for the disjoint conditional, and the retract equation of a, repeated on the inner sum.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.32).** ` (a ⊕ b) ∘ inleft ∘ a : a ∘→ (a ⊕ b) `. -/
theorem eq_4_32 {a b : Pomega} (ha : IsRetract a) :
    typed (comp (plusR a b) (comp inleftC a)) (arrowR a (plusR a b)) := by
  change comp (plusR a b) (comp inleftC a) =
    funOf (arrowR a (plusR a b)) (comp (plusR a b) (comp inleftC a))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inleftC_app, retract_app ha]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_zero, retract_app ha]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero, retract_app ha]

end DomainTheory.DataTypesAsLattices
