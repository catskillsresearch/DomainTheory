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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.swapProdT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Pairing up, as a function out of `T`.** `pairToFun(x, y) : T → E` sends `t ↦ cond(t, x,
y)`; in particular `true ↦ x`, `false ↦ y`, `⊥ ↦ ⊥` (Exercise 3.26). -/
noncomputable def pairToFun : ApproximableMap (prod E E) (funSpace TD E) :=
  curry ((cond E).comp swapProdT)

end Prod

end DomainTheory.NeighbourhoodSystems
