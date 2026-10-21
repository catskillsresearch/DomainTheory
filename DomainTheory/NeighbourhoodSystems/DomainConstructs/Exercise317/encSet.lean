/-ai
The encoding of a binary string is the set of index-token pairs such that, whenever the string defines a bit at that index, the token lies in the bit neighbourhood of that bit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Token
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.bitNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `encSet σ ⊆ ℕ × {0,1}`: pin copy `i` to `bitNbhd σ[i]` for `i < |σ|`, free otherwise. -/
def encSet (σ : Str) : Set (ℕ × Token) := {p | ∀ b, σ[p.1]? = some b → p.2 ∈ bitNbhd b}

end DomainTheory.NeighbourhoodSystems.Exercise317
