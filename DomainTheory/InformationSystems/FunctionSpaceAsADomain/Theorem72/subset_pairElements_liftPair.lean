module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftLeft
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap






















theorem subset_pairElements_liftPair {x : A.Element} {y : B.Element}
    {u : Finset α} {v : Finset β} (hu : ↑u ⊆ x.carrier) (hv : ↑v ⊆ y.carrier) :
    ↑(liftPair A B u v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  have hp' : p ∈ liftLeft A B u ∪' liftRight A B v := Finset.mem_coe.1 hp
  rcases mem_funion.mp hp' with hp | hp
  · exact subset_pairElements_liftLeft A B hu (Finset.mem_coe.2 hp)
  · exact subset_pairElements_liftRight A B hv (Finset.mem_coe.2 hp)

end InfoSys
end DomainTheory.InformationSystems
