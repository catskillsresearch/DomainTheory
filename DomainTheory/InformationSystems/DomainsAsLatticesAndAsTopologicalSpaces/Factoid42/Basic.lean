/-ai
This module gathers and re-exports the binary meet together with the carrier and the element obtained by intersecting a family, as the setting for Factoid 4.2. The intersection of any nonempty family of elements is again an element, so the set of elements is a conditionally complete inf-semilattice.
ai-/
module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInfCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42.familyInf

@[expose] public section

/-!
# Factoid 4.2 — conditional completeness for meets

**Factoid 4.2 (Scott §4).** For any *non-empty* family of elements, the set-theoretic
intersection of the family is again an element. Thus `|A|` is a conditionally complete
inf-semilattice.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


end InfoSys
end DomainTheory.InformationSystems
