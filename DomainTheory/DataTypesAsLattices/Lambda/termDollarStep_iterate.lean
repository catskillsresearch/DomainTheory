/-ai
The double application of the n-th iterate from bottom of the term-level dollar step, at u and z, equals the n-th finite stage of the sequence revaluation of u at z.

Proceed by induction on n. At zero, the iterate is bottom, application of bottom is bottom, and the zero stage of the sequence is bottom. At a successor, rewrite by the two-argument application law and the definition of the body, apply the inductive hypothesis, and use the successor law for the finite stage.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_bot
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_zero
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_succ_term
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_app2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termDollarStep_iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot termDollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, termDollarStep_app2, termDollarStepBody, ih, seqFunLt_succ_term]

end DomainTheory.DataTypesAsLattices
