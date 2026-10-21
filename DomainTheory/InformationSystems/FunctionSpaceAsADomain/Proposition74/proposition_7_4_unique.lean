/-ai
Scott's Proposition 7.4, uniqueness: an element that is fixed by an approximable endomap and lies below every pre-fixed point equals the least fixed point. The fixed-point equation is Plotkin's clause (ii), and leastness is the least-fixed-point property of Theorem 7.3.

The fixed-point equality is turned into the pre-fixed-point inequality, and that inequality together with the leastness hypothesis is passed to the uniqueness lemma for the least fixed point.
ai-/
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


/-- **Proposition 7.4.** Uniqueness via the Theorem 7.3 least-fixed-point property
(Plotkin’s (ii) is the fixed-point equation; leastness is 7.3(iii)). -/
theorem proposition_7_4_unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
