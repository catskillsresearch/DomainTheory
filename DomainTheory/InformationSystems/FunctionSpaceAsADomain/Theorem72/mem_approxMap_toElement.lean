/-ai
A function token belongs to the element associated with an approximable map if and only if the map relates the token's input set to its output set.

The two sides are the same proposition, so the equivalence is reflexivity of logical equivalence.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


theorem mem_approxMap_toElement (f : ApproximableMap A B) {p : FunToken A B} :
    p ∈ (approxMap_toElement A B f).carrier ↔ f.rel p.val.1 p.val.2 :=
  Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
