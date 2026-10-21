/-ai
The identity approximable map sends the bottom element to itself. Strictness of the identity makes the naturality clause of Scott's Proposition 7.4 a tautology when the mediating map is the identity.

The proof is the evaluation law for the identity map at the bottom element.
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


/-- Identity is strict, so 7.4(iii) specializes to a tautology on `fix` itself. -/
theorem idMap_botElement : (idMap A).toElement A.botElement = A.botElement :=
  idMap_toElement A A.botElement

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
