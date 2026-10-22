/-ai
Every Kleene approximant of a retract functor that preserves strictness is strict.

The zero stage is strict by the bottom application law. A successor stage is strict by the preservation hypothesis, using that the preceding stage is a retract and, inductively, strict.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_botElem
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Strictness of all Kleene approximants of a strictness-preserving
retract functor. -/
theorem iterateBot_isStrict {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a)) :
    ∀ n, IsStrict (iterateBot F n)
  | 0 => by simp [iterateBot, IsStrict, funOf_botElem]
  | n + 1 =>
      hstrict _ (iterates_areRetracts hret n)
        (iterateBot_isStrict hret hstrict n)

end DomainTheory.DataTypesAsLattices
