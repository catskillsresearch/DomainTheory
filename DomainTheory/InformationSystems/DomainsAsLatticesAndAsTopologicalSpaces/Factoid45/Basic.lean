/-ai
This file gathers and re-exports the finite approximants of an element, the directed suprema of Factoid 4.4, and Factoid 3.6, as the setting for Scott's Factoid 4.5, in which finite elements are compact and every element is the directed least upper bound of the finite elements below it.
ai-/

module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid44
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45.finiteApproximants

@[expose] public section

/-!
# Factoid 4.5 — algebraicity via finite elements

**Factoid 4.5 (Scott §4).** Finite elements `ū` are compact, and every element is the
directed lub of the finite elements below it (algebraicity). The carrier identity
`x = ⋃{ū | u ⊆ x}` is Factoid 3.6; here we package directedness, the lub form, and
compactness.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
