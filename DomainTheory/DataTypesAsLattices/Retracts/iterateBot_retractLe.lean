/-ai
Comparable Kleene stages of a strictness-preserving, retract-monotone retract functor stand in the retract order.

Induct along the inequality of indices. Equal stages are related by reflexivity, since each stage is a retract. A successor step composes the inductive inequality with the adjacent projection inequality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe_refl
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe_trans
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Projection equations between arbitrary comparable Kleene stages. -/
theorem iterateBot_retractLe {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    {n m : ℕ} (hnm : n ≤ m) :
    retractLe (iterateBot F n) (iterateBot F m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact retractLe_refl (iterates_areRetracts hret n)
  | succ m _ ih =>
      exact retractLe_trans ih (iterateBot_retractLe_succ hret hstrict hmono m)

end DomainTheory.DataTypesAsLattices
