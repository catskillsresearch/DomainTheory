module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.proposition_5_3
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.proposition_6_2
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftPair

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem sndFinset_liftPair (u : Finset α) (v : Finset β) :
    sndFinset A B (liftPair A B u v) =
      sndFinset A B (liftLeft A B u) ∪' v := by
  unfold liftPair
  rw [sndFinset.funion, liftRight.sndFinset_eq]

end InfoSys

end DomainTheory.InformationSystems
