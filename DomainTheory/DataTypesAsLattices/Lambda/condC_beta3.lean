/-ai
A third application of the conditional combinator, at z, equals the conditional of z, x, and y.

Rewrite by the second beta law, then beta-reduce, using Scott continuity of the conditional in its left argument.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condC_beta3 (x y z : Pomega) :
    funOf (funOf (funOf condC x) y) z = condSet z x y := by
  rw [condC_beta2]
  exact beta (condSet_isScottContinuous_left x y) z

end DomainTheory.DataTypesAsLattices
