/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
