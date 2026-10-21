/-ai
Scott 1976, (2.28). The least fixed point of the section g(x) unfolds as Y(g(x)) = g(x)(Y(g(x))).

This is the fixed-point equation for the Scott-continuous map y ↦ g(x, y).
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


























/-- **Scott 1976, (2.28).** Least-fixed-point unfolding `Y(g(x)) = g(x)(Y(g(x)))`. -/
theorem eq_2_28 {g : Pomega → Pomega → Pomega}
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    fix (g x) = g x (fix (g x)) :=
  (theorem_1_4 (hgy x)).1.symm

end DomainTheory.DataTypesAsLattices
