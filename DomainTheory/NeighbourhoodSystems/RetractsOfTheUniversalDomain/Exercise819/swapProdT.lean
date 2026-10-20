/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- The "swap" map `(E×E)×T → T×(E×E)`, used to feed `cond`'s `T×E×E`-shaped domain from a
`(E×E)×T`-shaped one so it can be curried away from the `T`-argument. -/
noncomputable def swapProdT : ApproximableMap (prod (prod E E) TD) (prod TD (prod E E)) :=
  paired (proj₁ (prod E E) TD) (proj₀ (prod E E) TD)

end Prod

end DomainTheory.NeighbourhoodSystems
