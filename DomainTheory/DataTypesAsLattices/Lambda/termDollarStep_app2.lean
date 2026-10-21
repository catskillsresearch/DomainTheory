/-ai
Applying the term-level dollar step at s first to u and then to z equals the body at s, u, and z.

Rewrite by the one-argument application law, then apply the β-law to the continuity of the body in z.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_z
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termDollarStep_app2 (s u z : Pomega) :
    funOf (funOf (termDollarStep s) u) z = termDollarStepBody s u z := by
  rw [termDollarStep_app]
  exact beta (termDollarStepBody_isScottContinuous_z s u) z

end DomainTheory.DataTypesAsLattices
