module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- `fTok p q = tok((D + (D×E)))` for `D = {p}`, `E = {q}`: `{Λ} ∪ 0p ∪ 1(gTok p q)`, equivalently
`gTok p (gTok p q)`. -/
def fTok (p q : Set Str) : Set Str := gTok p (gTok p q)

end Exercise624

end DomainTheory.NeighbourhoodSystems
