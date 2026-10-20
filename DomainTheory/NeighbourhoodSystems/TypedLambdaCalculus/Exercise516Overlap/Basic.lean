module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Overlap

@[expose] public section

/-!
# Exercise 5.16 follow-up (Scott 1981, PRG-19, Lecture V) — overlap-freeness of `t`

The second Thue–Morse property Scott asks for: `t` is **overlap-free**, `t ≠ u·a·a·a·v` for any
finite `u` and nonempty `a`. This is a self-contained theorem of combinatorics on words (Thue 1912);
it uses **no domain theory** (only the parity recurrences `tm (2n) = tm n`, `tm (2n+1) = ¬ tm n` of
the bit-function `tm` from `Exercise516ThueMorse`) and has no leverage from Mathlib, so it is proved
from scratch here.

We phrase an **overlap** of period `p ≥ 1` at offset `i` as a factor of length `2p+1` with period
`p`: `Overlap i p := 1 ≤ p ∧ ∀ k ≤ p, tm (i+k) = tm (i+p+k)`. The main theorem `no_overlap` shows no
overlap exists, and `overlap_free` is Scott's literal cube form `t ≠ u·a·a·a·v` (an overlap is
weaker than a cube, so the cube form follows).

The proof is the classical descent: the two base facts are *no three consecutive equal symbols*
(`no_three_consec`, the period-1 case) and a direct period-3 computation; an even period `2q`
contracts to a period-`q` overlap via the substitution structure, and an odd period `≥ 5` forces a
run of three equal symbols.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems

/-! ### The two basic facts about consecutive symbols. -/

/-! ### Index reductions for `tm`. -/

/-! ### Overlaps. -/


/-! ### Cube-freeness — Scott's literal form `t ≠ u·a·a·a·v`. -/

open Example44 ExampleB NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Exercise516
