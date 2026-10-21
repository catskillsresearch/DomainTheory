/-ai
If an approximable map h commutes with endomaps f and g, then g applied to the image under h of the least fixed point of f lies below that image.

Commutation of composition with evaluation rewrites the left-hand side as h applied to f of the fixed point, and Proposition 7.4(ii) replaces f of the fixed point by the fixed point itself.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.proposition_7_4_ii

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem toElement_comp_fix_le (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    g.toElement (h.toElement (fixElement A f)) ≤ h.toElement (fixElement A f) := by
  have h1 : g.toElement (h.toElement (fixElement A f)) =
      h.toElement (f.toElement (fixElement A f)) := by
    rw [← comp_toElement, ← hcomm, comp_toElement]
  rw [h1, proposition_7_4_ii A f]

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
