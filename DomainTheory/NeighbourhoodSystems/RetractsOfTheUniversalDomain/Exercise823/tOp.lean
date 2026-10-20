/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.uniqueFixedConstMapBot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}

/-- **Scott's `t(a)`**: the operator `t : (E → E) → (E → E)` induced by an approximable self-map
`t` of the function space `funSpace E E`, applied to an actual map `a : E → E`. -/
def tOp (t : ApproximableMap (funSpace E E) (funSpace E E)) (a : ApproximableMap E E) :
    ApproximableMap E E :=
  toApproxMap (t.toElementMap (toFilter a))

end Exercise823

end DomainTheory.NeighbourhoodSystems
