module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem iterateFrom_bot (f : Pomega → Pomega) (n : ℕ) :
    iterateFrom f botElem n = iterateBot f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateFrom, iterateBot, ih]

end DomainTheory.DataTypesAsLattices
