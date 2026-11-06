module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamRhs_eq_sum_function

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_82 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α),
      lamRhs A = sumSystem A (functionSystem (lambdaSystem A) (lambdaSystem A)) :=
  @lamRhs_eq_sum_function

end DomainTheory.InformationSystems.InfoSys
