/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}

/-- **Definition 8.3, first clause (Scott 1981, PRG-19).** A retraction `a : E → E` is a
*projection* provided `a ⊑ I_E`. (We do not separately require `IsRetraction a` in the
definition, matching Scott's usage where "projection" is applied to a retraction already in
hand; the conjunction is spelled out where needed, e.g. `IsFinitaryProjection`.) -/
def IsProjection (a : ApproximableMap E E) : Prop := IsRetraction a ∧ a ≤ idMap E

end DomainTheory.NeighbourhoodSystems
