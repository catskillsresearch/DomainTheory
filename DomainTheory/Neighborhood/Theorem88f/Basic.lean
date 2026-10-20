/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88e
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Proposition612

/-!
# Theorem 8.8(b)(vii)(4) — the projection pair `D'' ⊴ U` is computable

`Theorem88e.lean` (Part 7's third sub-part) assembled `D'' := DprimeUCode P`, `D ≅ᴰ D''`, and
`D'' ◁ U`, with `D''`'s own `ComputablePresentation` (`DprimeUCodePresentation`, master index `0`,
`X n := Yc P n = UX (YseqCode P n)`). This file supplies the actual headline claim of Theorem
8.8(b)(vii): the projection pair `i := (D'' ◁ U).inj`/`j := (D'' ◁ U).proj` (Proposition 6.12) is
**computable** (Definition 7.2, `IsComputableMap`) relative to `DprimeUCodePresentation`/
`UComputablePresentation`.

## Why this is now easy

Both relations unfold (`Subsystem.inj_rel`/`Subsystem.proj_rel`) to a `mem`-clause on each side
*plus* a raw subset test — and every `mem`-clause is automatically true once both sides are read off
their own presentations (`⟨n, rfl⟩` for `D''`, `U_mem_UX` for `U`), so `i`/`j`'s relations reduce to
exactly

* `i`: `Yc P n ⊆ UX m`, i.e. `UX (YseqCode P n) ⊆ UX m`;
* `j`: `UX m ⊆ Yc P n`, i.e. `UX m ⊆ UX (YseqCode P n)`;

both instances of the single **generic** fact `Xₙ ⊆ Xₘ` is recursively decidable for *any*
`ComputablePresentation` (`ComputablePresentation.incl_computable`, Definition 7.1), here applied to
`UComputablePresentation` and reindexed along the `Nat.Primrec` function `YseqCode P`
(`primrec_YseqCode`, Theorem 8.8(b)(vii)(2)) in one argument. No new `Nat.Primrec` machinery, no new
decidability core — the entire content is packaging two reindexings of `incl_computable`, decidable
hence r.e. (`RecDecidable.re`).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
end DomainTheory.Neighborhood
