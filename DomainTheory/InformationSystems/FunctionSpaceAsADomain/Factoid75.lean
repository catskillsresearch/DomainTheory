module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.conditional_iso

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys
open ApproximableMap

theorem theorem_75 :
    ∀ {α : Type*} [DecidableEq α] (A : InfoSys α) (x y : A.Element),
      (condMap A x y).toElement boolTrue = x ∧
      (condMap A x y).toElement boolFalse = y ∧
      ∀ (f : ApproximableMap boolSystem A), IsStrict boolSystem A f →
        f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) :=
  @conditional_iso

end DomainTheory.InformationSystems.InfoSys
