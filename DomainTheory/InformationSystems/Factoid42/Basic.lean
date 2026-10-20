/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Factoid41
public import DomainTheory.InformationSystems.Factoid42.familyInfCarrier
public import DomainTheory.InformationSystems.Factoid42.familyInf

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
