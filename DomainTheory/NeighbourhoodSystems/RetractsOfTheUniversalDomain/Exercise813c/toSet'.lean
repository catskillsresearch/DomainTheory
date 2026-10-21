/-ai
The map from the Lindenbaum algebra to sets of points of Cantor space sends the class of a formula to its Cantor-space evaluation. The quotient lift is well-defined because semantically equivalent formulas have equal Cantor-space evaluations.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.semanticEquiv_iff_evalSet'_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- `Lindenbaum`'s canonical map to Cantor-space clopens, the counterpart of `8.13(b)`'s
`Lindenbaum.toSet`. -/
def Lindenbaum.toSet' : Lindenbaum → Set (ℕ → Bool) :=
  Quotient.lift evalSet' fun _ _ h => semanticEquiv_iff_evalSet'_eq.mp h

end DomainTheory.NeighbourhoodSystems
