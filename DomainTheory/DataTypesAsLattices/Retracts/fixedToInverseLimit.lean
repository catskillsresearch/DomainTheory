/-ai
A fixed point of the least fixed point of F determines the inverse-limit sequence whose nth term is the nth iterate of F from the empty set, applied to that fixed point. Each term is typed because the iterates are retracts, and consecutive terms agree because each iterate lies below the next in the retract order, so the projection equation at the point simplifies by the law of composition. The construction assumes that F preserves retracts, strictness, and the retract order.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp_app
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.iterates_areRetracts
public import DomainTheory.DataTypesAsLattices.Retracts.iterateBot_retractLe_succ
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- A point of the fixed-point range determines its sequence of finite
projections. -/
def fixedToInverseLimit {F : Pomega → Pomega}
    (_hf : IsScottContinuous F)
    (hret : ∀ a, Retract a → Retract (F a))
    (hstrict : ∀ a, Retract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, Retract a → IsStrict a →
      Retract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (u : Fixpoints (funOf (fix F))) : RetractInverseLimit F :=
  ⟨fun n => funOf (iterateBot F n) u.1,
    ⟨fun n => (retract_app (iterates_areRetracts hret n) u.1).symm,
      fun n => by
        have hle := iterateBot_retractLe_succ hret hstrict hmono n
        have happ := congrArg (fun a => funOf a u.1) hle.1
        simpa only [comp_app] using happ⟩⟩

end DomainTheory.DataTypesAsLattices
