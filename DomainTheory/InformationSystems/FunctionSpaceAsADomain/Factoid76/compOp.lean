/-ai
The composition operator from the product of the function spaces from B to C and from A to B into the function space from A to C is the currying of the uncurried composition map.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

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
