module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Proposition74.Basic

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem proposition_7_4_unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
