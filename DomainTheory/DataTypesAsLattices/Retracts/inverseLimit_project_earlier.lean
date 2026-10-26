module

public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
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

/-- Earlier typed coordinates are fixed by every later projection. -/
theorem inverseLimit_project_earlier {F : Pomega → Pomega}
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {m n : ℕ} (hmn : m ≤ n) :
    funOf (iterateBot F n) (v.1 m) = v.1 m := by
  have hle := iterateBot_retractLe hret hstrict hmono hmn
  have hm : funOf (iterateBot F m) (v.1 m) = v.1 m :=
    (v.property.1 m).symm
  have happ := congrArg (fun a => funOf a (v.1 m)) hle.2
  simpa only [comp_app, hm] using happ.symm

end DomainTheory.DataTypesAsLattices
