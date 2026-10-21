/-ai
The conditional of elements x and y evaluates to x at the Boolean element true and to y at the Boolean element false, and every strict approximable map from the Boolean system is the conditional of its values at true and false.

The numbered name theorem_75 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.conditional_iso

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_75.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst)
  (x y : @DomainTheory.InformationSystems.InfoSys.Element α inst A),
  And
    (@Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
        DomainTheory.InformationSystems.InfoSys.BoolToken α
        DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
        DomainTheory.InformationSystems.InfoSys.boolSystem A
        (@DomainTheory.InformationSystems.InfoSys.condMap α inst A x y)
        DomainTheory.InformationSystems.InfoSys.boolTrue)
      x)
    (And
      (@Eq (@DomainTheory.InformationSystems.InfoSys.Element α inst A)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
          DomainTheory.InformationSystems.InfoSys.BoolToken α
          DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
          DomainTheory.InformationSystems.InfoSys.boolSystem A
          (@DomainTheory.InformationSystems.InfoSys.condMap α inst A x y)
          DomainTheory.InformationSystems.InfoSys.boolFalse)
        y)
      (∀
        (f :
          @DomainTheory.InformationSystems.InfoSys.ApproximableMap DomainTheory.InformationSystems.InfoSys.BoolToken α
            DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
            DomainTheory.InformationSystems.InfoSys.boolSystem A),
        @DomainTheory.InformationSystems.InfoSys.IsStrict DomainTheory.InformationSystems.InfoSys.BoolToken α
            DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
            DomainTheory.InformationSystems.InfoSys.boolSystem A f →
          @Eq
            (@DomainTheory.InformationSystems.InfoSys.ApproximableMap DomainTheory.InformationSystems.InfoSys.BoolToken
              α DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
              DomainTheory.InformationSystems.InfoSys.boolSystem A)
            f
            (@DomainTheory.InformationSystems.InfoSys.condMap α inst A
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
                DomainTheory.InformationSystems.InfoSys.BoolToken α
                DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
                DomainTheory.InformationSystems.InfoSys.boolSystem A f DomainTheory.InformationSystems.InfoSys.boolTrue)
              (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
                DomainTheory.InformationSystems.InfoSys.BoolToken α
                DomainTheory.InformationSystems.InfoSys.instDecidableEqBoolToken inst
                DomainTheory.InformationSystems.InfoSys.boolSystem A f
                DomainTheory.InformationSystems.InfoSys.boolFalse)))) :=
  @DomainTheory.InformationSystems.InfoSys.conditional_iso

end DomainTheory.InformationSystems.InfoSys
