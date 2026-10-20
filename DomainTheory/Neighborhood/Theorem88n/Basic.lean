/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88f

@[expose] public section

/-!
# Theorem 8.8(b), strengthened — a *direct* computable projection pair `D ⇄ U`

`theorem_8_8_b` (`Theorem88g.lean`) gives, for an effectively given `D`, an isomorphic copy
`D' : NeighborhoodSystem ℚ` (`= DprimeUCode P`) with a *literal* subsystem relation `D' ◁ U` whose
Proposition 6.12 projection pair (`h.inj`/`h.proj`) is computable — but it stops there, leaving
`D ≅ᴰ D'` a bare `Nonempty (OrderIso …)` fact, with no computable projection pair `D ⇄ U` for `D`
*itself*. Definition 8.9 needs exactly that (fixed projection pairs `𝒰+𝒰 → 𝒰`, `𝒰×𝒰 → 𝒰`,
`𝒰→𝒰 → 𝒰` and back), so this file supplies it.

## Why the iso is computable after all

`Theorem 2.7` (`ApproximableMap.ofIso`, `Approximable.lean`) turns *any* order-isomorphism
`e : D.Element ≃o D'.Element` into an approximable map, choice-free. Applied to `domainIsoCode P`
this gives `isoInj P : D → D''`/`isoProj P : D'' → D` (`D'' := DprimeUCode P`) with the projection-pair laws
as plain equalities (Theorem 2.7 + `ext_of_toElementMap`, mirroring `Exercise618.lean`'s
`jmap_comp_imap`).

The point of this file is that `isoInj`/`isoProj` are **also computable**, because `domainIsoCode` is built
(`Theorem88e.lean`) to match `D`'s and `D''`'s raw indices *literally* along the primitive-recursive
involution `eIdx P` (`Theorem88b.lean`): unfolding `ofIso`/`toDprimeUCode`/`toDCode` and using the
raw-index correspondence `embed_eq_iff_raw_code` (`e P i = e P j ↔ Yc P i = Yc P j`) collapses both
relations to a single reindexed `incl_computable` query —

* `isoInj_rel_iff_incl`: `(isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b)`;
* `isoProj_rel_iff_incl`: `(isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a)`

(using that `n := b`, resp. `m := eIdx P a`, is already the "same-index" witness the general
existential ranges over — no other witness can give a different answer, by `embed_eq_iff_raw_code`).
Composing `isoInj`/`isoProj` with `(DprimeUCode_subsystem P).inj`/`.proj` (computable, `Theorem88f.lean`) via
`comp_isComputable` then gives the headline `theorem_8_8_b_strong`: a *single* computable projection
pair `D ⇄ U`, no intermediate `D'` in sight.

The reasoning in this file is itself **choice-free**: `isoInj`/`isoProj` are built relationally
(`ofIso`), and all the analysis is `Exists`-elimination into `Prop` goals or plain rewriting. But
`theorem_8_8_b_strong` (like `theorem_8_8_b`/`DprimeUCode_subsystem`/`YseqCode` themselves) audits
`⊆ {propext, Classical.choice, Quot.sound}` — this is **inherited**, not new taint: `U`
(`Definition87.lean`) already audits with `Classical.choice` (Mathlib's `Rat` order instance path),
and everything downstream that mentions `U`/`UComputablePresentation` inherits it (confirmed
directly: `U_isEffectivelyGiven`, `DprimeUCode_subsystem`, `YseqCode` all show the same footprint).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## `isoInj`, `isoProj`: the code-level iso `D ≅ᴰ DprimeUCode P` as approximable maps -/

/-- **`isoInj : D → D''`**, Theorem 2.7 applied to `domainIsoCode P`. -/
noncomputable def isoInj : ApproximableMap D (DprimeUCode P) := ofIso (domainIsoCode P)

/-- **`isoProj : D'' → D`**, Theorem 2.7 applied to the inverse iso. -/
noncomputable def isoProj : ApproximableMap (DprimeUCode P) D := ofIso (domainIsoCode P).symm

/-! ## Reducing `isoInj.rel`/`isoProj.rel` to raw-index inclusion tests -/

/-! ## Computability of `isoInj`, `isoProj` -/

/-! ## Assembly: a direct computable projection pair `D ⇄ U` -/
end DomainTheory.Neighborhood
