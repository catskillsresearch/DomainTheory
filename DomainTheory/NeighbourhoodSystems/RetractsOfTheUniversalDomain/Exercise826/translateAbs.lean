/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Scott's translation recipe for a `λ`-abstraction**, `λx^{D_a}.σ ↦ λx. b(σ'[a(x)/x])`: given
the further-translated body `body : E → E` (Scott's `σ'`, the untyped realization of `σ` as a
function of `x`), form the projection-sandwiched abstraction `b∘body∘a`. Stated for an arbitrary
neighbourhood system `E` and arbitrary `a, b : E → E` — specializes to Scott's `𝒰`/finitary
projections, but needs nothing special about `E`. -/
def translateAbs (a b body : ApproximableMap E E) : ApproximableMap E E :=
  b.comp (body.comp a)

end DomainTheory.NeighbourhoodSystems
