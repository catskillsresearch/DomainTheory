module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeRhs

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_81 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α),
      treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  @treeRhs.eq_sum_product

end DomainTheory.InformationSystems.InfoSys
