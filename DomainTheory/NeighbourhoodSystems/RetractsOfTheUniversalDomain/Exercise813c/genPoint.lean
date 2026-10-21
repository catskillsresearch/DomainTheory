/-ai
The coordinate set at a natural number is the set of points of Cantor space whose value at that coordinate is true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- The `i`-th coordinate-projection basic clopen of Cantor space `ℕ → Bool`: the literal
transcription, on this carrier, of `8.13(a)`'s `generator i`. -/
def genPoint (i : ℕ) : Set (ℕ → Bool) := (fun x : ℕ → Bool => x i) ⁻¹' {true}

end DomainTheory.NeighbourhoodSystems
