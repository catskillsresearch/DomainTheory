/-ai
The box determined by a finite set of coordinates and a Boolean function is the set of points of Cantor space that agree with that function on every coordinate in the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- The basic clopen pinning every coordinate in `I` to match `f`, and leaving the rest free —
the standard basis element of the product topology on `ℕ → Bool`. -/
def box (I : Finset ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) := {x | ∀ i ∈ I, x i = f i}

end DomainTheory.NeighbourhoodSystems
