/-ai
The map into the terminal one-point domain is the default approximable map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The unique map to the terminal object, named. -/
def toUnit : ApproximableMap V unitSys := default

end DomainTheory.NeighbourhoodSystems
