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
