/-ai
The pairing operator from the product of the function spaces from C to A and from C to B into the function space from C to the product of A and B is the currying of the uncurried pairing map.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOpUncurry

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- **Factoid 7.6.** Operator `pair : (C → A) × (C → B) → (C → A × B)`. -/
def pairOp : ApproximableMap
    (productSystem (functionSystem C A) (functionSystem C B))
    (functionSystem C (productSystem A B)) :=
  curryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
    (pairOpUncurry A B C)

end InfoSys

end DomainTheory.InformationSystems
