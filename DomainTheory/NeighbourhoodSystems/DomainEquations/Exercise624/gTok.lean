module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- `gTok p q = tok((D + E))` for `D = {p}`, `E = {q}`: the tagged union `{Λ} ∪ 0p ∪ 1q`. It is also
the master of the product `{p} × {q}` (sum and product share the master shape over `{0,1}*`). -/
def gTok (p q : Set Str) : Set Str := insert ([] : Str) (embBit false p ∪ embBit true q)

end Exercise624

end DomainTheory.NeighbourhoodSystems
