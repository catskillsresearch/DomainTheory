/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise825Unit.Basic
public import DomainTheory.Neighborhood.Exercise825Unit.isomorphic_of_unique

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}




/-- **Exercise 8.25 (Scott 1981, PRG-19) — the obstruction `𝟙 → 𝟙 = 𝟙`.** The terminal one-point
domain is a fixed point of `→`, carrying no information: this is why "the obvious solution by
retracts is of no use". -/
theorem funSpace_unitSys_isomorphic : funSpace unitSys unitSys ≅ᴰ unitSys :=
  isomorphic_of_unique _ _

end DomainTheory.Neighborhood
