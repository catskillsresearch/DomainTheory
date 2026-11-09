module

public import DomainTheory.InformationSystems.SomeDomainEquations.treeSystem

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

open treeSystem

theorem example_8_1 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α),
      treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  @treeRhs.eq_sum_product

end DomainTheory.InformationSystems.InfoSys
