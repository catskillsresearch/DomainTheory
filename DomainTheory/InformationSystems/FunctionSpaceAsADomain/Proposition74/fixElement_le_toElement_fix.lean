module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.toElement_comp_fix_le

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem fixElement_le_toElement_fix (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    fixElement B g ≤ h.toElement (fixElement A f) :=
  fixElement_le_of_pre_fixed B g (h.toElement (fixElement A f))
    (toElement_comp_fix_le A B f g h hcomm)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
