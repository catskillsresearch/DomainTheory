module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurry_curryMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- **Factoid 7.6.** Operator `comp : (B → C) × (A → B) → (A → C)`. -/
def compOp : ApproximableMap
    (productSystem (functionSystem B C) (functionSystem A B))
    (functionSystem A C) :=
  curryMap (productSystem (functionSystem B C) (functionSystem A B)) A C
    (compOpUncurry A B C)

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem compOp.uncurry :
    uncurryMap (productSystem (functionSystem B C) (functionSystem A B)) A C (compOp A B C) =
      compOpUncurry A B C := by
  simp only [compOp, uncurry_curryMap]

end InfoSys
end DomainTheory.InformationSystems
