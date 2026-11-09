module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.proposition_5_3
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.proposition_6_2
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.applyMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurryMap
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.rel_input_output_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funCon_of_approxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.ProdCon_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.fstFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndFinset_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.entSet_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.rel_of_funTokens
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funCon_of_curry_pointwise

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem liftRight_funion (v v' : Finset β) :
    liftRight A B (v ∪' v') = liftRight A B v ∪' liftRight A B v' := by
  ext p
  constructor
  · intro hp
    rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
    rcases funion.mem.mp hy with hy | hy
    · exact funion.mem.mpr (Or.inl ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
    · exact funion.mem.mpr (Or.inr ((liftRight.mem A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases funion.mem.mp hp with hp | hp
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inl hy), rfl⟩
    · rcases (liftRight.mem A B).1 hp with ⟨y, hy, rfl⟩
      exact (liftRight.mem A B).2 ⟨y, funion.mem.mpr (Or.inr hy), rfl⟩

end InfoSys
end DomainTheory.InformationSystems
