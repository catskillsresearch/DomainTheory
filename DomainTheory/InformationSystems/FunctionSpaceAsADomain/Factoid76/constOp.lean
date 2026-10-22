module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- **Factoid 7.6.** Operator `const : B → (A → B)`, as `curry fst`. -/
def constOp : ApproximableMap B (functionSystem A B) :=
  curryMap B A B (fstMap B A)

end InfoSys

end DomainTheory.InformationSystems
