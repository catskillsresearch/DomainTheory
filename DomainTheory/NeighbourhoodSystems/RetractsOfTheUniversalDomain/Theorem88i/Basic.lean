/-ai
This file gathers and re-exports the diagonal fixed-point predicate, its agreement with membership in the fixed-neighbourhood subsystem, its recursive enumerability, the primitive-recursive witness characteristic extracted from that enumerability, the gated fold and its one-step function, their code-level versions, and the fact that the fold of the empty list is the master index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStepCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_nil

@[expose] public section

/-!
# Theorem 8.8(c), Part 2 of 6 — a `qChar`-gated primitive-recursive fold landing back in `DiagFixed`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 1 (`Theorem88h.lean`) produced, from a
computable map `a`, a `{0,1}`-valued primitive-recursive `qChar` with `DiagFixed P a n ↔ ∃i,
qChar⟨i,n⟩ = 1`. This file builds the **fold** that will let Part 3 enumerate `fixedNbhd a`: a
primitive-recursive list-fold whose accumulator is *always* a raw index already satisfying
`DiagFixed`, no matter what list it is fed — so no unbounded search is ever needed once `qChar` (an
r.e., not decidable, fact) has been supplied per list entry as a *checked* witness pair.

## Design (mirroring `DAtomDecidable.lean`'s `meetStep`/`meetFold`/`meetFoldCode`, simplified)

Each list entry `e` codes a pair `⟨i, n⟩ = Nat.pair i n`: `n` is a candidate raw index and `i` is a
*claimed* `qChar`-witness for it. One step of the fold (`myStep`), given the current accumulator `r`
(already known — by the invariant — to satisfy `DiagFixed`) and the next entry `e`:

* checks `qChar e = 1` (this literally checks `qChar (Nat.pair i n) = 1`, so — reading `hqChar`
  backwards — witnesses `DiagFixed P a n` for `n := e.unpair.2`, no unbounded search needed since the
  witness `i` was *given*, not searched for);
* checks the `V`-consistency decider `cons (Nat.pair r n) = 1` (i.e. `∃k, X k ⊆ Xᵣ ∩ Xₙ`);
* if **both** succeed, advances the accumulator to `P.inter r n` (which lands back in `DiagFixed` by
  `fixedNbhd_subsystem`'s `inter_closed`, since `Xᵣ ∩ Xₙ` is then both a genuine `V`-neighbourhood
  *and* an intersection of two `fixedNbhd a`-neighbourhoods);
* otherwise **no-ops**, leaving the accumulator at `r` unchanged (unlike `meetStep`'s permanent
  "not ok" freeze — here an invalid or inconsistent entry is simply *skipped*, since we are not
  trying to prove anything about the *particular* list fed in, only that whatever comes out the other
  end is still `DiagFixed`).

The base case is `P.masterIdx`, always `DiagFixed` since `a.master_rel : a.rel V.master V.master`
transported along `P.masterIdx_spec`. No `(ok, idx)` pair is needed in the accumulator (unlike
`meetStep`) precisely because a bad entry is dropped rather than remembered.

`myStepCode`/`myFoldCode` package `myStep`/`myFold` at the `Nat.Primrec` level via the existing
`foldCode` combinator (`Recursive.lean`); `Nat.Primrec` is immediate from `primrec_foldCode` given
`qChar`, `cons`, and `P.inter` are all primitive recursive. The headline result,
`diagFixed_myFoldCode`, is the invariant "`DiagFixed P a (myFoldCode qChar cons c)` for every list-code
`c`" — Part 3 will show this enumeration is *onto* `fixedNbhd a`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Recursive.lean`'s
choice-free `foldCode`/`selectFn`/`isOne` machinery and `Theorem85.lean`'s choice-free
`fixedNbhd_subsystem`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-! ### The fold, at the `Set`/`List` level -/




variable {P qChar cons}

variable (P qChar cons)

/-! ### Code-level `myFold`, and its primitive recursivity -/


end DomainTheory.NeighbourhoodSystems
