/-ai
The n-th iterate of the dollar step from ⊥, applied to u and then to z, equals sequence revaluation of u at z truncated below n.

The zeroth iterate agrees with the empty stage by the application of ⊥ and the zero clause of the truncation. At a successor, the double application is the step body, the induction hypothesis replaces the recursive call, and the successor clause of the truncation matches that body.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_bot
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_app2
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_zero
public import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_succ

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











































theorem dollarStep_iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot dollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, dollarStep_app2, dollarStepBody, ih, seqFunLt_succ]

end DomainTheory.DataTypesAsLattices
