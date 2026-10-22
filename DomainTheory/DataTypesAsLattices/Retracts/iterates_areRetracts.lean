/-ai
If a map preserves retracts, every Kleene approximant is a retract.

The zero stage is the bottom retract. A successor stage is the image of the preceding retract under the preservation hypothesis.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.bot_isRetract

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem iterates_areRetracts {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a)) :
    ∀ n, Retract (iterateBot F n)
  | 0 => by simpa [iterateBot] using bot_isRetract
  | n + 1 => by simpa [iterateBot] using hret _ (iterates_areRetracts hret n)

end DomainTheory.DataTypesAsLattices
