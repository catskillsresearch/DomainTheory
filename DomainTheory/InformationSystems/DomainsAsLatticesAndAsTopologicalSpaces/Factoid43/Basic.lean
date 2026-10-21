/-ai
This module gathers and re-exports finite consistency, deductive closure, the carrier union of a family, the family join, the binary join, and the finite entailment witness for a subset of a deductive closure, as the setting for Factoid 4.3. The join of a family exists exactly when the union of the carriers is finitely consistent, in which case the join is the deductive closure of that union, and a binary join exists exactly when some element bounds both arguments.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.IsFinitelyConsistent
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.deductiveClosure
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familyUnionCarrier
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.familySup
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.join
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.exists_entSet_of_subset_deductive

@[expose] public section

/-!
# Factoid 4.3 — consistent joins

**Factoid 4.3 (Scott §4).** The join of a family of elements exists in `|A|` iff the
union of their carriers is finitely consistent; in that case the join is the deductive
closure of the union. Binary case: `x ⊔ y` exists iff some element bounds both.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)






end InfoSys
end DomainTheory.InformationSystems
