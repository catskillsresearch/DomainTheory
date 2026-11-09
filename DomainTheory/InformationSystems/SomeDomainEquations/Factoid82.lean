module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lambdaSystem

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem example_8_2 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α),
      lamRhs A = sumSystem A (functionSystem (lambdaSystem A) (lambdaSystem A)) :=
  @lamRhs_eq_sum_function

end DomainTheory.InformationSystems.InfoSys
