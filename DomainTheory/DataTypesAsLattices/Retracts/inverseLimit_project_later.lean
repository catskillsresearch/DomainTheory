/-ai
Every later coordinate of a coherent inverse-limit sequence projects to an earlier one under the earlier Kleene stage.

Induct along the inequality of indices. At equal indices the coordinate is fixed by its own stage. At a successor, the retract order of the stages supplies a projection equation; apply it at the successor coordinate, rewrite composition by the successor coherence equation, and use the inductive hypothesis.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Repeated coherence: every later coordinate projects to an earlier one. -/
theorem inverseLimit_project_later {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
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
