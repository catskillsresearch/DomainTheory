module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xorStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_isComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_lowXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lowXor_eq_mod
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_xorStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_myXor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xor_low_rec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xorStep_iter_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myXor_eq_xor
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_myAndNot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_diff_same_level
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_myDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff_iff_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_diff_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff_spec

@[expose] public section

/-!
# Exercise 8.12(f), prerequisite — `V` has a computable set-difference (`IsComputableDiff`)

`Exercise812d.lean`'s `IsComputableDiff` (`(d)(3)(a)`) has so far only been instantiated for `U`
(`Exercise812eD.lean`'s `U_isComputableDiff`/`Udiff`). This file supplies the missing `V`-side
instance, `V_isComputableDiff`, needed by `8.12(f)`'s `splitFromBisection VComputablePresentation
… UComputableBisection` (`V` is the *prober* for `(f)`, symmetric to `U` being the prober for
`(e)`).

## Design

Mirrors `LevelSetPrimrec.lean`'s `VinterRaw`/`Vinter` exactly, substituting `Exercise812c.lean`'s
`levelSet_diff` for `levelSet_myInter` as the driving mathematical fact. `levelSet_diff`'s formula
combines two upsampled masks via the bitwise "and-not" identity `a ^^^ (a &&& b)`
(`testBit_xor_and_self`) instead of plain `&&&` — so the one new piece of `Nat.Primrec`
infrastructure needed is a computable version of that combinator. Rather than re-deriving the
"and-not" identity arithmetically, we build a fresh choice-free primitive-recursive bitwise XOR
(`myXor`), mirroring `myLand`/`myLor` bit-for-bit (`lowXor`/`xorStep`, `Nat.testBit_xor` in place of
`Nat.testBit_and`/`Nat.testBit_lor`), and simply compose it with the already-`Pass` `myLand`:
`myAndNot a b := myXor a (myLand a b)` realizes `a ^^^ (a &&& b)` for free from
`myXor_eq_xor`/`myLand_eq_land`, no new arithmetic identity needed.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-! ## A choice-free primitive-recursive bitwise XOR (`myXor`)

Mirrors `myLand` (`LevelSetPrimrec.lean`) bit-for-bit: `lowXor`/`xorStep` in place of
`lowAnd`/`landStep`, `Nat.testBit_xor` in place of `Nat.testBit_and`. -/











/-! ## The "and-not" combinator `myAndNot a b = a ^^^ (a &&& b)` -/




/-! ## `VdiffRaw`/`Vdiff` — `V`'s computable set-difference

Mirrors `VinterRaw`/`Vinter` exactly, substituting `levelSet_diff` (`Exercise812c.lean`) for
`levelSet_myInter` and `myAndNot` for `myLand`. -/












end DomainTheory.NeighbourhoodSystems
