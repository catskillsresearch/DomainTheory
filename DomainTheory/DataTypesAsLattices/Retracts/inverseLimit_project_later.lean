module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Repeated coherence: every later coordinate projects to an earlier one. -/
theorem inverseLimit_project_later {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {n m : ℕ} (hnm : n ≤ m) :
    funOf (iterateBot F n) (v.1 m) = v.1 n := by
  induction m, hnm using Nat.le_induction with
  | base => exact (v.property.1 n).symm
  | succ m hnm ih =>
      have hle := iterateBot_retractLe hret hstrict hmono hnm
      have happ :=
        congrArg (fun a => funOf a (v.1 (m + 1))) hle.1
      rw [comp_app, ← v.property.2 m, ih] at happ
      exact happ

end DomainTheory.DataTypesAsLattices
