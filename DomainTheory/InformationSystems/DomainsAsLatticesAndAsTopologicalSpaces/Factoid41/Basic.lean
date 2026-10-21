/-ai
This module gathers and re-exports the elements of an information system and their binary meet by intersection, as the setting for Factoid 4.1. The set of elements is an inf-semilattice under intersection, the order is equality with a meet, the meet is idempotent, commutative, and associative, and the bottom element is a zero for the meet.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.inf

@[expose] public section

/-!
# Factoid 4.1 — `|A|` is an inf-semilattice under intersection

**Factoid 4.1 (Scott §4 / inventory).** The intersection of two elements is again an
element, so `|A|` is an inf-semilattice under `∩`. In particular
`x ⊆ y ↔ x ∩ y = x`. Scott also records that `∩` is idempotent, commutative, and
associative, and that `⊥` is a zero for `∩`.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
