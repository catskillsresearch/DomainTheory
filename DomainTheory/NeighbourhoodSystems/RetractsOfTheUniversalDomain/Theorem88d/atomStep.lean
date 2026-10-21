/-ai
The one-step transition reads the current index and the packed state from its argument. The bit is the remainder modulo 2. The candidate codes prepend that index to the positive list and to the negative list. Two emptiness checks test those refinements. The new state halves the remainder, selects the positive and negative codes by the bit, and selects the new U-code by the bit and the two checks: an empty refinement yields the code 0, a refinement that already exhausts the atom carries the old code, and a genuine split takes the left or right split of the old code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.wY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.wState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode_packState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

/-- **The per-step state transition.** `datomDec` should be `DAtom_recDecidable (P0 P)`'s extracted
decider (`datomDec (pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅`);
kept abstract here so `Nat.Primrec`-ness can be proved once and reused. `bit := remK % 2`, then:
`posC' := pair y posC + 1` / `negC' := pair y negC + 1` are the candidate accumulators with the
current index `y` prepended; `emptyI`/`emptyJ` decide whether the "+"/"-"-refinements are already
`D`-side empty; the new `U`-code either stays `0` (junk, `D`-side empty), is carried over unchanged
(the refinement equals the old atom outright), or is `splitULeft`/`splitURight` of the old code
(a genuine split). -/
def atomStep (datomDec : ℕ → ℕ) (w : ℕ) : ℕ :=
  let y := wY w
  let s := wState w
  let bit := stateRem s % 2
  let posC' := Nat.pair y (statePos s) + 1
  let negC' := Nat.pair y (stateNeg s) + 1
  let emptyI := datomDec (Nat.pair posC' (stateNeg s))
  let emptyJ := datomDec (Nat.pair (statePos s) negC')
  packState (stateRem s / 2) (selectFn bit posC' (statePos s)) (selectFn bit (stateNeg s) negC')
    (selectFn bit
      (selectFn emptyI 0 (selectFn emptyJ (stateCode s) (splitULeft (stateCode s))))
      (selectFn emptyJ 0 (selectFn emptyI (stateCode s) (splitURight (stateCode s)))))

end AtomCode

end DomainTheory.NeighbourhoodSystems
