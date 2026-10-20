/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Exercise 8.14 (Scott 1981, PRG-19), the definition.** A retraction `a : E → E` is a
*closure operator* iff `I_E ⊑ a`, i.e. `a` is inflationary. -/
def IsClosureOperator (a : ApproximableMap E E) : Prop := IsRetraction a ∧ idMap E ≤ a

end DomainTheory.NeighbourhoodSystems
