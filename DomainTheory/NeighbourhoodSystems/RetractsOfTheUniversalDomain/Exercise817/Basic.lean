/-ai
If a neighbourhood system is isomorphic to a second system, and the second embeds in a third, then the first embeds in the third.

Unfold the embedding as a subsystem of the third isomorphic to the second system, and compose that isomorphism with the isomorphism of the first system with the second.

The embedding relation is transitive.

Unfold the two embeddings as a subsystem of the middle system and a subsystem of the last system. Those subsystem relations, and the isomorphism of the middle system with its copy, become projection pairs, and their composite is a projection pair from the first copy into the last system. That pair is an embedding, and transporting it along the isomorphism of the first system with its copy yields the composite embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ProjPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ofIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.IsUniversal

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

/-!
# Exercise 8.17 (Scott 1981, PRG-19)

> **Exercise 8.17.** Find explicitly (if possible) the projection pairs for `𝒰+𝒰`, `𝒰×𝒰`, and
> `𝒰→𝒰` needed for 8.9. Are any of these domains isomorphic with `𝒰`? (The author does not know a
> really good construction for `𝒰→𝒰`.) Find a universal domain `V ≠ 𝒰`.

## What is formalized here

**Part 1** (projection pairs for 8.9) is already fully answered by `Definition89.lean`: `iPlus/jPlus`,
`iTimes/jTimes`, `iArrow/jArrow` are exactly computable projection pairs `𝒰+𝒰 ⇄ 𝒰`, `𝒰×𝒰 ⇄ 𝒰`,
`𝒰→𝒰 ⇄ 𝒰` (via `theorem_8_8_b_strong`), so this file only *restates* them under §8.17's name, and
adds the free bonus corollary `sumUU_trianglelefteq_U`/`prodUU_trianglelefteq_U`/
`funSpaceUU_trianglelefteq_U : (·) ⊴ 𝒰` (Lemma 6.15 applied to those exact pairs).

**Part 3** (a universal domain `V ≠ 𝒰`) is answered in full: Exercise 8.12's `V` (a *different*
`NeighborhoodSystem`, over `ℕ` rather than `𝒰`'s `ℚ`, built from `2^kℕ+ℓ`) is effectively isomorphic
to `𝒰` (`effectiveIso812_UV`), hence — since universality (`𝒰`'s defining property, Theorem 8.8(a))
transports along isomorphism — `V` is *also* universal (`V_isUniversal`). This needed one genuinely
new general-purpose tool, **`⊴` is transitive** (`trianglelefteq_trans`), built by composing
`ProjectionPair`s (a new `ProjectionPair.comp`, plus `ProjectionPair.ofIso` turning any `DomainIso`
into a projection pair via Theorem 2.7's `ofIso`) — surprisingly, `⊴`'s transitivity was not yet in
the codebase despite being an obviously expected structural fact.

**Part 2** (are `𝒰+𝒰`/`𝒰×𝒰`/`𝒰→𝒰` isomorphic to `𝒰`?) is **deliberately left open/deferred** here,
documented rather than guessed at: what we get for free is only the *one-directional* embeddings
`𝒰+𝒰, 𝒰×𝒰, 𝒰→𝒰 ⊴ 𝒰` (bonus corollaries above). Establishing genuine *isomorphism* `𝒰+𝒰 ≅ 𝒰` (or
`×`) would need a **converse embedding plus a back-and-forth argument** of the same scale as Exercise
8.12's 7-part, ~2000-line development (`arxiv.md`'s Exercise 8.12 row: "order isos preserve
compactness... so `U≅V` is not just tedious to build, it needs a genuinely different technique").
Scott's own parenthetical — "the author does not know a really good construction for `𝒰→𝒰`" — flags
that even *he* did not resolve the `→` case; we do not attempt to go further than Scott here. This is
therefore recorded as a clearly-scoped deferral, not a `sorry`.

Everything proved in this file is **choice-free** (`⊆ {propext, Quot.sound}`) except where it merely
*mentions* `U`/`V` (which inherit `Classical.choice` from `Definition87.lean`'s `Rat`-order-instance
provenance, the same footprint as every other `U`-mentioning headline theorem in this project).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## A general tool: `⊴` is transitive (not yet in the codebase)

`Subsystem.ProjectionPair` (`Proposition612.lean`) is deliberately single-token-type (`D E :
NeighborhoodSystem α`), since it is built for the *homogeneous* `D ◁ E` case. `⊴`'s projection pairs
are heterogeneous (`i : ApproximableMap D E`, `j : ApproximableMap E D`, possibly different token
types), so we bundle a small local heterogeneous analogue, `ProjPair`, purely as scaffolding for
`trianglelefteq_trans` below. -/





/-- **`D ⊴ E` composed with an isomorphism `D ≅ᴰ D'` on the left is still `D ⊴ E`** — immediate
from unfolding `⊴` and composing the two `DomainIso`s (`OrderIso.trans`). -/
theorem trianglelefteq_of_isomorphic_left {D : NeighborhoodSystem α} {D' : NeighborhoodSystem β}
    {E : NeighborhoodSystem γ} (hDD' : D ≅ᴰ D') (hD'E : D' ⊴ E) : D ⊴ E := by
  obtain ⟨F, hFE, ⟨eD'F⟩⟩ := hD'E
  obtain ⟨eDD'⟩ := hDD'
  exact ⟨F, hFE, ⟨eDD'.trans eD'F⟩⟩

/-- **`⊴` is transitive.** `D ⊴ E` and `E ⊴ F` give `D ⊴ F`: unfold both to a subsystem `D' ◁ E`
(`D ≅ᴰ D'`) and `E' ◁ F` (`E ≅ᴰ E'`); `ProjPair.ofSubsystem` turns `D' ◁ E`/`E' ◁ F` into projection
pairs, `ProjPair.ofIso` turns `E ≅ᴰ E'` into one too, and composing all three (`ProjPair.comp`) gives
a projection pair `D' ⇄ F`, hence `D' ⊴ F` (Lemma 6.15). Gluing back `D ≅ᴰ D'` on the left
(`trianglelefteq_of_isomorphic_left`) finishes. -/
theorem trianglelefteq_trans {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (h1 : D ⊴ E) (h2 : E ⊴ F) : D ⊴ F := by
  obtain ⟨D', hD'E, ⟨eDD'⟩⟩ := h1
  obtain ⟨E', hE'F, ⟨eEE'⟩⟩ := h2
  have pD'F : ProjPair D' F :=
    ((ProjPair.ofSubsystem hD'E).comp (ProjPair.ofIso eEE')).comp (ProjPair.ofSubsystem hE'F)
  have hD'F : D' ⊴ F :=
    trianglelefteq_of_projectionPair pD'F.inj pD'F.proj pD'F.proj_comp_inj pD'F.inj_comp_proj_le
  exact trianglelefteq_of_isomorphic_left ⟨eDD'⟩ hD'F

/-! ## Part 1 — the projection pairs for `𝒰+𝒰`, `𝒰×𝒰`, `𝒰→𝒰` needed for 8.9 -/

/-! ## Part 3 — a universal domain `V ≠ 𝒰` -/

end DomainTheory.NeighbourhoodSystems
