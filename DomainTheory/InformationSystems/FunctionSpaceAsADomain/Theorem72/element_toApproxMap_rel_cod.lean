/-ai
If the relation recovered from a function-space element holds of an input set and an output set, then the output set is consistent.

The consistency witness is read off the existential hypothesis.
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

/-- Codomain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_cod (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      v ∈ B.Con :=
  fun ⟨_, hv, _⟩ => hv

end InfoSys

end DomainTheory.InformationSystems
