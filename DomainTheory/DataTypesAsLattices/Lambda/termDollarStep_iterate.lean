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
