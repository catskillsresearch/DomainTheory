module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- `fTok` is monotone in both arguments. -/
theorem fTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : fTok p q ⊆ fTok p' q' :=
  gTok_mono hp (gTok_mono hp hq)

end Exercise624
end DomainTheory.NeighbourhoodSystems
