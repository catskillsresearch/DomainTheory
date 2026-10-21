/-ai
The self-consistent family of every element of the universal domain is nonempty. The witness is the master neighbourhood, which sub relates to itself and which belongs to the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scFamily

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

instance instNonemptyScFamily (t : U.Element) : Nonempty (scFamily t) :=
  ⟨⟨U.master, subU.master_rel, t.master_mem⟩⟩

end DomainTheory.NeighbourhoodSystems
