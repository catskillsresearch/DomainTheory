/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.isoOfUnique

@[expose] public section

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), obstruction — `𝟙 → 𝟙 = 𝟙`

Scott's exercise asks first to notice that the "obvious" solution of `D ≅ D → D` by retracts of the
universal domain `𝒰` is of no use, because `1 → 1 = 1` for projections: the *only* finitary
projection whose fixed-point domain is the terminal one-point domain `𝟙` is (up to the trivial
retract structure) itself again `𝟙`, so iterating the "solve `D ≅ D → V`" method starting from the
smallest possible `V = 𝟙` produces nothing but `𝟙` again — the recursion is stuck at the bottom of
the lattice of projections and never escapes to a non-trivial domain.

This file records the precise domain-level fact behind Scott's remark: `𝟙` is a fixed point of the
function-space construction, `(𝟙 → 𝟙) ≅ 𝟙`. Both `𝟙`'s own element poset and the poset of
approximable self-maps of `𝟙` are one-point (`Unique`), and any two `NeighborhoodSystem`s whose
element posets are both `Unique` are trivially isomorphic (`isoOfUnique`) — there is only one
order-isomorphism type on a singleton. This is exactly why Scott says the naive approach is "of no
use": solving `D ≅ D → 𝟙` by the fixed-point method (Exercise 8.23, with `T(a) := 𝟙` constantly)
would converge to `D = 𝟙`, which trivially satisfies `𝟙 ≅ 𝟙 → 𝟙` but carries no information — hence
Scott's instruction to "change the method", starting instead from the much larger `𝒰^∞` in place of
`𝟙`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`): the only inputs are
`Unique`/`Subsingleton` reasoning and the existing `funSpaceEquiv` bijection.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


/-- **There is only one approximable self-map of `𝟙`, the identity.** Both maps induce the same
(unique) elementwise function, so `ext_of_toElementMap` identifies them. -/
instance uniqueApproximableMapUnitSys : Unique (ApproximableMap unitSys unitSys) where
  default := idMap unitSys
  uniq _f := ApproximableMap.ext_of_toElementMap fun _x => Subsingleton.elim _ _

/-- **`(𝟙 → 𝟙)` has a unique element**, transported from the unique approximable self-map of `𝟙`
along `funSpaceEquiv`. -/
instance uniqueFunSpaceUnitSys : Unique (funSpace unitSys unitSys).Element where
  default := (funSpaceEquiv unitSys unitSys).symm default
  uniq _x := (funSpaceEquiv unitSys unitSys).injective (Subsingleton.elim _ _)
end DomainTheory.NeighbourhoodSystems
