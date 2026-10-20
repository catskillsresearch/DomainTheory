/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812_UV

@[expose] public section

/-!
# Exercise 8.12(g)(4) (Scott 1981, PRG-19, Lecture VIII) — final assembly: `U ≅ V`

The exercise's ultimate target: `U` and `V` are effectively isomorphic. A one-line instantiation of
`Exercise812d.lean`'s generic `effectiveIso812d` (`(d)(6)`'s `EffectiveIso` assembly), fed every
concrete `U`/`V` fact this development has built:

* `(e)(d)`/`(f)`: `U_isComputableDiff`/`V_isComputableDiff`, `splitX812e`/`isComputableSplit_812e`,
  `splitX812f`/`isComputableSplit_812f`;
* `(g)(3)`: `hxSplit812e : SplitSpec' V splitX812e`, `hySplit812f : SplitSpec' U splitX812f`
  (`Exercise812eD.lean`/`Exercise812f.lean`, completed above);
* `(c)`: `U_isPositive`/`U_diffClosed`/`U_noMinimal`, `V_isPositive`/`V_diffClosed`/`V_noMinimal`;
* `(g)(1)`: `U_master_nonempty`/`UX_zero`, `V_master_nonempty`/`VX_zero`;
* `(g)(2)`: `U_isComputableUnion`, `V_isComputableUnion`.

No new proof content — every subgoal `effectiveIso812d` demands was already discharged by one of
the above. -/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem Exercise718


end DomainTheory.NeighbourhoodSystems
