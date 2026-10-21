/-ai
This file gathers and re-exports the computable unions of U and V: list concatenation on U, with its primitive recursiveness, the decoding of appended codes, raw equality, membership, specification, existence, and decidability, and bitwise disjunction on V, with the level-set union law, the raw and canonical primitive recursiveness, the specifications, existence, and decidability.

If some index presents the union of the neighbourhoods indexed by n and by m, then the canonical union index presents that same union.

The numbered name example_812_g2 is that statement.
ai-/
module

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

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion_spec'

end DomainTheory.NeighbourhoodSystems
