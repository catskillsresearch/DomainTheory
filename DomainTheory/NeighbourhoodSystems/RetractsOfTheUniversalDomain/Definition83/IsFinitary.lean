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

/-- **Definition 8.3, second clause (Scott 1981, PRG-19).** A retraction `a : E → E` is *finitary*
iff its fixed-point set `{y ∈ |E| ∣ a(y) = y}` — ordered by the inherited inclusion `⊑` — is
isomorphic to (the element poset of) some neighbourhood system. -/
def IsFinitary (a : ApproximableMap E E) : Prop :=
  ∃ (β : Type u) (F : NeighborhoodSystem β),
    Nonempty ({y : E.Element // a.toElementMap y = y} ≃o F.Element)

end DomainTheory.NeighbourhoodSystems
