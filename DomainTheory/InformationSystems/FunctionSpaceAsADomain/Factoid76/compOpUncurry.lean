/-ai
The uncurried composition map, from the product of the product of the function spaces from B to C and from A to B with A, into C, applies the map from B to C to the result of applying the map from A to B to the element of A. It is application after the pairing of the first projection of the function pair with the application of the second projection to the element of A.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- Uncurried composition: `((B→C)×(A→B)) × A → C`. -/
def compOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem B C) (functionSystem A B)) A) C :=
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B
      (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A))))

end InfoSys

end DomainTheory.InformationSystems
