/-ai
The extracted emptiness decider sends a code to the zero-one wrapper of the chosen primitive recursive D-atom decider of the re-pointed presentation. The wrapper makes the result literally 0 or 1, so the later selections on an emptiness check take their zero branch exactly on the nonempty side.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode_packState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The extracted `D`-atom-emptiness decider for `P0 P`.** Obtained non-constructively
(`Classical.choice`, via `RecDecidable`'s bare existential) from `DAtom_recDecidable (P0 P)`; the
resulting *function* is exactly as computable as any other `Nat.Primrec` function in this
codebase — only *naming* it needs choice, mirroring `DprimeUPresentation`'s own `noncomputable`.
Wrapped in `isOne` so the result is *literally* `{0,1}`-valued (not just "`= 1` iff ..."): `(vii)(1)`'s
`selectFn`-based case analysis on `emptyI`/`emptyJ` needs the *exact* value `0` on the false side, not
merely `≠ 1` (`selectFn`, unlike a genuine `if`, is only well-behaved on a literal `0`/`1` condition). -/
noncomputable def datomDec : ℕ → ℕ := fun n => isOne ((DAtom_recDecidable (P0 P)).choose n)

end DomainTheory.NeighbourhoodSystems
