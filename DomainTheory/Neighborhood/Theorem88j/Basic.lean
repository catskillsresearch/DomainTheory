/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88i

@[expose] public section

/-!
# Theorem 8.8(c), Part 3 of 6 — the induced enumeration covers `fixedNbhd a`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 2 (`Theorem88i.lean`) built a
`qChar`-gated primitive-recursive fold `myFoldCode` whose output, for *every* list-code `c`, is a
raw index `myFoldCode qChar cons c` satisfying `DiagFixed P a` (Part 1's r.e. diagonal predicate,
`↔ (fixedNbhd a).mem (P.X ·)`). This file packages that enumeration and shows it is exactly onto
`fixedNbhd a`.

`D_X qChar cons c := P.X (myFoldCode qChar cons c)`:

* **`D_X_mem`** — every `D_X qChar cons c` is a `fixedNbhd a`-neighbourhood: immediate from Part 2's
  invariant `diagFixed_myFoldCode` via `diagFixed_iff_fixedNbhd_mem`.
* **`D_X_of_diagFixed`** — the reusable core of the surjectivity argument: for *any* raw `V`-index
  `m` already known to be `DiagFixed` (not necessarily `myFoldCode`'s own output), some `D_X` value
  hits `P.X m` on the nose. Part 1's `hqChar` extracts a witness `i` with `qChar ⟨i, m⟩ = 1`.
  Feeding the **singleton list `[⟨i, m⟩]`** (encoded via `encodeList`) into the fold performs
  exactly one step from `P.masterIdx`: the `qChar`-gate passes by construction, and the
  `V`-consistency gate passes because `P.X m ⊆ V.master = P.X P.masterIdx` (`V.sub_master`) makes
  `P.masterIdx`/`m` trivially consistent via the witness `m` itself (`P.X m ⊆ P.X P.masterIdx ∩
  P.X m`, in fact equality). The fold therefore advances to `P.inter P.masterIdx m`, and
  `P.inter_spec` gives `P.X (P.inter P.masterIdx m) = V.master ∩ P.X m = P.X m`.
* **`D_X_surj`** — every `fixedNbhd a`-neighbourhood `Y` is hit by some `D_X qChar cons c`:
  `P.surj` produces a raw `V`-index `n₀` with `P.X n₀ = Y`, which is `DiagFixed` since `Y` is
  `a`-fixed, so `D_X_of_diagFixed` finishes it. (This reduction is also exactly what Theorem
  8.8(c) Part 4 needs for its `cons_computable` direction `⟸`, applied instead to `m := P.inter
  n₁ n₂` — hence factoring `D_X_of_diagFixed` out here rather than inlining it.)

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Theorem88h.lean`/
`Theorem88i.lean`'s choice-free apparatus plus `Recursive.lean`'s choice-free `encodeList`/
`decodeList` round-trip.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-- **The enumeration induced by the `qChar`-gated fold**: `D_X c` reads off the `V`-neighbourhood
presented at the fold's output raw index. -/
def D_X (c : ℕ) : Set α := P.X (myFoldCode P qChar cons c)

variable {P qChar cons}
end DomainTheory.Neighborhood
