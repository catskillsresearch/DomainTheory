module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeSystem

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem example_8_1 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α),
      treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  @treeRhs.eq_sum_product

end DomainTheory.InformationSystems.InfoSys
