module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- The pair iteration `Φ(p, q) = (fTok p q, gTok p q)` from the bottom pair `({Λ}, {Λ})`. -/
def pIter : ℕ → Set Str × Set Str
  | 0 => ({([] : Str)}, {([] : Str)})
  | n + 1 => (fTok (pIter n).1 (pIter n).2, gTok (pIter n).1 (pIter n).2)

end Exercise624

end DomainTheory.NeighbourhoodSystems
