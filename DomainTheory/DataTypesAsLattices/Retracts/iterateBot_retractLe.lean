module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe_refl
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe_trans
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe_succ

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Projection equations between arbitrary comparable Kleene stages. -/
theorem iterateBot_retractLe {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    {n m : ℕ} (hnm : n ≤ m) :
    retractLe (iterateBot F n) (iterateBot F m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact retractLe_refl (iterates_areRetracts hret n)
  | succ m _ ih =>
      exact retractLe_trans ih (iterateBot_retractLe_succ hret hstrict hmono m)

end DomainTheory.DataTypesAsLattices
