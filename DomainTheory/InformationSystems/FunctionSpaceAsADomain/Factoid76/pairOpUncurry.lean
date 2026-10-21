/-ai
The uncurried pairing map sends the pair of a pair of maps, from C to A and from C to B, with an element of C to the pair of the two maps applied to that element. It pairs the application of the first component to the element with the application of the second component to the element.
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

/-- Uncurried pairing: `((C→A)×(C→B)) × C → A×B`. -/
def pairOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem C A) (functionSystem C B)) C)
    (productSystem A B) :=
  let P := productSystem (functionSystem C A) (functionSystem C B)
  pairMap A B
    (comp (applyMap (B := C) (C := A))
      (pairMap (functionSystem C A) C
        (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))
    (comp (applyMap (B := C) (C := B))
      (pairMap (functionSystem C B) C
        (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))

end InfoSys

end DomainTheory.InformationSystems
