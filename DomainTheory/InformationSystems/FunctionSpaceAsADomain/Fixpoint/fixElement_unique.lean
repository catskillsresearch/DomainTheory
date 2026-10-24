
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_le_of_pre_fixed
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.toElement_fixElement_le

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


namespace ApproximableMap


/-- **Theorem 7.3.** Uniqueness of the least fixed-point operator on elements. -/
theorem fixElement_unique (f : ApproximableMap A A) (φ : A.Element)
    (hfix : f.toElement φ ≤ φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f := by
  apply le_antisymm
  · exact hleast _ (toElement_fixElement_le A f)
  · exact fixElement_le_of_pre_fixed A f φ hfix

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
