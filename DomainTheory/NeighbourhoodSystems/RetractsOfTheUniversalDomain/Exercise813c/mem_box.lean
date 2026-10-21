/-ai
A point lies in a box if and only if it agrees with the prescribed function on every pinned coordinate.

The two sides are definitionally the same.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.box

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

@[simp] theorem mem_box {I : Finset ℕ} {f x : ℕ → Bool} :
    x ∈ box I f ↔ ∀ i ∈ I, x i = f i := Iff.rfl

end DomainTheory.NeighbourhoodSystems
