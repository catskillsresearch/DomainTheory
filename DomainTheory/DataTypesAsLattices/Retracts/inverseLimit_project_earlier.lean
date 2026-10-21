/-ai
An earlier coordinate of a coherent inverse-limit sequence is fixed by every later Kleene projection.

The Kleene stages between the two indices stand in the retract order, so the earlier stage equals the composite of the later stage with the earlier stage. The earlier coordinate is fixed by its own stage. Apply that composite equation at the earlier coordinate and simplify composition.
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

namespace DomainTheory.DataTypesAsLattices

/-- Earlier typed coordinates are fixed by every later projection. -/
theorem inverseLimit_project_earlier {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {m n : ℕ} (hmn : m ≤ n) :
    funOf (iterateBot F n) (v.1 m) = v.1 m := by
  have hle := iterateBot_retractLe hret hstrict hmono hmn
  have hm : funOf (iterateBot F m) (v.1 m) = v.1 m :=
    (v.property.1 m).symm
  have happ := congrArg (fun a => funOf a (v.1 m)) hle.2
  simpa only [comp_app, hm] using happ.symm

end DomainTheory.DataTypesAsLattices
