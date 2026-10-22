module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamRhs_eq_sum_function

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_82.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst),
  @Eq
    (@DomainTheory.InformationSystems.InfoSys
      (DomainTheory.InformationSystems.InfoSys.SumToken α
        (@DomainTheory.InformationSystems.InfoSys.FunToken (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)))
      fun
        (a b :
          DomainTheory.InformationSystems.InfoSys.SumToken α
            (@DomainTheory.InformationSystems.InfoSys.FunToken
              (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
              (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
              (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
              (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
              (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))) =>
      @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α
        (@DomainTheory.InformationSystems.InfoSys.FunToken (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))
        inst
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken
          (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))
        a b)
    (@DomainTheory.InformationSystems.InfoSys.lamRhs α inst A)
    (@DomainTheory.InformationSystems.InfoSys.sumSystem α
      (@DomainTheory.InformationSystems.InfoSys.FunToken (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))
      inst
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken
        (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))
      A
      (@DomainTheory.InformationSystems.InfoSys.functionSystem
        (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.LamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqLamDToken α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.lambdaSystem α inst A))) :=
  @DomainTheory.InformationSystems.InfoSys.lamRhs_eq_sum_function

end DomainTheory.InformationSystems.InfoSys
