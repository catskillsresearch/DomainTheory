/-ai
The bottom element lies below the top element.

The bottom element of O lies below every element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `⊥ ⊑ ⊤`. -/
theorem botElt_le_topElt : botElt ≤ topElt := O.bot_le _

end DomainTheory.NeighbourhoodSystems.Exercise215
