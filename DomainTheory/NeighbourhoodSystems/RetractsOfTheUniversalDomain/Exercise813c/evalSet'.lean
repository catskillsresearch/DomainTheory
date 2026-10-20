module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- The *same* recursion as `evalSet`, but interpreted via `genPoint` instead of `generator`. -/
def evalSet' : Formula → Set (ℕ → Bool)
  | .var i => genPoint i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet' φ)ᶜ
  | .and φ ψ => evalSet' φ ∩ evalSet' ψ
  | .or φ ψ => evalSet' φ ∪ evalSet' ψ

end DomainTheory.NeighbourhoodSystems
