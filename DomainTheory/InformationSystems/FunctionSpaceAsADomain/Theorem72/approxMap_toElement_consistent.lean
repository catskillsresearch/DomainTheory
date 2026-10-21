/-ai
A finite set of function tokens lying in the relation of an approximable map is consistent in the function space.

The function-consistency lemma for an approximable map applies, because every token of the set lies in the relation.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_approxMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Consistency of the token-set of an approximable map. -/
theorem approxMap_toElement_consistent (f : ApproximableMap A B)
    (Y : Finset (FunToken A B))
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2}) :
    Y ∈ (functionSystem A B).Con :=
  funCon_of_approxMap A B f Y fun _ hp => hY (Finset.mem_coe.2 hp)

end InfoSys

end DomainTheory.InformationSystems
