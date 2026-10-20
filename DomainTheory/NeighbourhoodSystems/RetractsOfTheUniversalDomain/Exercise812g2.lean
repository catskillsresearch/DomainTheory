/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_isComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_isComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.decodeQPairList_appendListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_eq_union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_UX_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_exists
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VunionRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_union_exists
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_union_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec'

@[expose] public section

/-!
# Exercise 8.12(g)(2) — `IsComputableUnion` for `U` and `V`

`Exercise812d.lean`'s `(d)(4)(a)` defines `IsComputableUnion` (mirroring `IsComputableDiff`'s shape
for `∪` instead of `\`) but never instantiates it for either concrete system. Both instances turn
out **unconditional**: unlike `IsComputableDiff`'s `diffIdx_spec`, whose hypothesis is genuinely
needed (a difference can be empty), a union of two genuine, non-empty neighbourhoods is *always*
again a genuine neighbourhood for both `U` and `V` — so `unionIdx_spec`'s hypothesis, while still
accepted (to match the structure's shape), is never actually used, and `union_computable` reduces
to the trivial always-`1` decider.

* **`U`-side** (`Uunion`): mirrors `Exercise812eD.lean`'s `Udiff`, substituting the raw list-`++`
  primitive `appendListCode` (`Recursive.lean`) for `diffCode` — concatenation trivially witnesses
  `presentedIntervals`'s own closure under `∪` (`presentedIntervals_append`, `Definition87.lean`).
* **`V`-side** (`Vunion`): mirrors `LevelSetPrimrec.lean`'s `VinterRaw`/`Vinter`, substituting the
  bitwise-OR primitive `myLor` for `myLand` (`levelSet_myUnion`, the computable version of
  `Exercise812.lean`'s inlined union identity already used in `V_union_mem`).
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ## `U_isComputableUnion` -/










/-! ## `V_isComputableUnion` -/












end DomainTheory.NeighbourhoodSystems
