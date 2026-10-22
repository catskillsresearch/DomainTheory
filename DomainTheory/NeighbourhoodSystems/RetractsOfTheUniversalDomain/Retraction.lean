module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}

/-- **Definition 8.1 (Scott 1981, PRG-19).** A *retraction* of `E` is an approximable mapping
`a : E → E` with `a ∘ a = a`. -/
class Retraction (a : ApproximableMap E E) : Prop where
  out : a.comp a = a

end DomainTheory.NeighbourhoodSystems
