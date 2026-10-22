
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


/-- **Theorem 7.3.** `fix(f)` is a fixed point. -/
theorem fixElement_fixed (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f := by
  apply le_antisymm
  · exact toElement_fixElement_le A f
  · have hpre : f.toElement (f.toElement (fixElement A f)) ≤
        f.toElement (fixElement A f) :=
      toElement_mono f (toElement_fixElement_le A f)
    exact fixElement_le_of_pre_fixed A f (f.toElement (fixElement A f)) hpre

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
