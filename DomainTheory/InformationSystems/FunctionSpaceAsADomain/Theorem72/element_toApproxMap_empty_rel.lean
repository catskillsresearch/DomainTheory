/-ai
The empty input set and the empty output set determine a function token that lies in every function-space element. That token is the bottom token of the function space.

The empty consistency witnesses are used, and Factoid 3.2 places the bottom token in the carrier.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- The empty pair is related. -/
theorem element_toApproxMap_empty_rel (x : (functionSystem A B).Element) :
    ∃ (hu : (∅ : Finset α) ∈ A.Con) (hv : (∅ : Finset β) ∈ B.Con),
      mkFunToken A B ∅ ∅ hu hv ∈ x.carrier := by
  refine ⟨A.con_empty, B.con_empty, ?_⟩
  change funBot A B ∈ x.carrier
  exact factoid_3_2 (functionSystem A B) x

end InfoSys

end DomainTheory.InformationSystems
