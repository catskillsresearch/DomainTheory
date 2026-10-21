/-ai
The union of a coherent inverse-limit sequence is typed by the least fixed point of the functor: the union equals the least fixed point applied to the union.

Unfold the least fixed point and the application of a union, and match coordinates. Each coordinate equation is the projection of the union at that stage.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_iUnion

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The union of a coherent sequence lies in the range of the least fixed
point retract. -/
theorem inverseLimit_iUnion_typed {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) :
    typed (⋃ n, v.1 n) (fix F) := by
  change (⋃ n, v.1 n) = funOf (fix F) (⋃ n, v.1 n)
  rw [fix, funOf_iUnion]
  apply Eq.symm
  congr 1
  funext n
  exact inverseLimit_project_iUnion hf hret hstrict hmono v n

end DomainTheory.DataTypesAsLattices
