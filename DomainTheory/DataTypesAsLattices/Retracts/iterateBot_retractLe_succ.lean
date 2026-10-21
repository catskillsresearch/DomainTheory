/-ai
Adjacent Kleene stages of a strictness-preserving, retract-monotone retract functor stand in the retract order.

The zero stage lies below the next stage because that next stage is strict, so the bottom retract lies below it. A successor step applies the monotonicity hypothesis to the retract and strictness facts for the two adjacent stages and to the inductive inequality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.bot_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_isStrict

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Projection-order monotonicity gives adjacent projection equations for
the Kleene chain. -/
theorem iterateBot_retractLe_succ {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    ∀ n, retractLe (iterateBot F n) (iterateBot F (n + 1))
  | 0 => by
      simpa [iterateBot] using
        (bot_retractLe (iterateBot_isStrict hret hstrict 1))
  | n + 1 => by
      simpa only [iterateBot] using
        hmono (iterates_areRetracts hret n) (iterateBot_isStrict hret hstrict n)
          (iterates_areRetracts hret (n + 1))
          (iterateBot_isStrict hret hstrict (n + 1))
          (iterateBot_retractLe_succ hret hstrict hmono n)

end DomainTheory.DataTypesAsLattices
