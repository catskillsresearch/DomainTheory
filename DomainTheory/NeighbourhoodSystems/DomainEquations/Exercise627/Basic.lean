/-ai
The composite of the left projection after the left injection is the identity map of D₀. The composite of the left injection after the left projection lies below the identity map of the coalesced sum. Therefore D₀ embeds as a subdomain of the coalesced sum of D₀ and D₁.

A composite through the injection and then the projection supplies two inclusions of leftN, and the leftN subset criterion turns their composite into an inclusion in D₀. Conversely, an inclusion X ⊆ Z in D₀ is witnessed by the intermediate neighbourhood leftN of X, which belongs to the coalesced sum: the injection meets it by a reflexive inclusion, and the projection meets Z by the subset criterion. A composite the other way supplies two inclusions of coalesced neighbourhoods through leftN, and the composite of those inclusions is the identity relation on the coalesced sum. The embedding is the projection-pair criterion applied to these two composite laws.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstProj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inlInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inlProj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictify
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strctMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.twoPt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.unitPt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.embF_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_proper
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.X_eq_master_of_nil_mem_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.subset_of_embF_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.X_eq_master_of_embT_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplus_mem_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct_mono

@[expose] public section

/-!
# Exercise 6.27 (Scott 1981, PRG-19, §6) — which subsystem relations hold

> **EXERCISE 6.27.** Which of the following relationships are true:
> `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`;  `𝒟 ⊴ 𝒟 × ℰ`;
> `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`;  `𝒟 ⊴ 𝒟 ⊕ ℰ`;
> `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)`;  `𝒟 ⊴ 𝒟 ⊗ ℰ` ?

Here `⊴` is Scott's *embeds-as-a-subdomain* relation of Lemma 6.15 (`Trianglelefteq`): `D ⊴ E`
means `D ≅ᴰ D'` for some `D' ◁ E`. We use the concrete `{0,1}*` constructions of Exercises 6.19/6.21
(`sumTok`, `prodTok`, `oplusTok`, `otimesTok`) and the function spaces `funSpace` / `strictFun`.

**Answer.** The first five hold for all `𝒟, ℰ`; the last fails in general.

| relation | verdict | name |
| --- | --- | --- |
| `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)` | **true** | `otimes_trianglelefteq_prod` (in fact `otimesTok ◁ prodTok`) |
| `𝒟 ⊴ 𝒟 × ℰ` | **true** | `fst_trianglelefteq_prod` |
| `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)` | **true** | `oplus_trianglelefteq_sum` (in fact `oplusTok ◁ sumTok`) |
| `𝒟 ⊴ 𝒟 ⊕ ℰ` | **true** | `inl_trianglelefteq_oplus` |
| `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` | **true** | `strictFun_trianglelefteq_funSpace` |
| `𝒟 ⊴ 𝒟 ⊗ ℰ` | **false in general** | `not_trianglelefteq_otimes_unit` |

The smash product collapses the bottom: pairing anything with `⊥_ℰ` is `⊥`. So `𝒟` embeds in
`𝒟 ⊗ ℰ` only when `ℰ` contributes a (finite) non-bottom point; for the trivial `ℰ = 𝟙` we have
`𝒟 ⊗ 𝟙 ≅ 𝟙`, refuting the universal claim.

All parts are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`) except `(4)`
(`inl_trianglelefteq_oplus`), whose `oplus_mem_leftN` decides the genuinely-undecidable test
`X = Δ₀` over an arbitrary system and so depends on `Classical.choice`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## (1) `(𝒟 ⊗ ℰ) ◁ (𝒟 × ℰ)` — the smash is literally a subsystem of the product

The smash `otimesTok` has the *same* master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ = prodTokNbhd Δ₀ Δ₁` and its proper
neighbourhoods `prodTokNbhd X Y` (with `X ≠ Δ₀`, `Y ≠ Δ₁`) are a sub-family of the product's
neighbourhoods. The consistency clause is inherited because intersections stay off the boundary. -/

/-! ## (2) `𝒟 ⊴ 𝒟 × ℰ` — first-factor projection pair

`𝒟` is not literally a subsystem of `𝒟 × ℰ` (the neighbourhoods have a different shape), but it
embeds via the projection pair `i(X) = (X, ⊥)`, `j(W) = fst W`. Concretely we send `X ∈ 𝒟` to the
product neighbourhood `prodTokNbhd X Δ₁` (pair `X` with all of `ℰ`); the embedding/projection are the
two refinement relations against that neighbourhood, exactly as in Proposition 6.12. -/


/-! ## (3) `(𝒟 ⊕ ℰ) ◁ (𝒟 + ℰ)` — the coalesced sum is literally a subsystem of the sum

`oplusTok` drops the improper copies `0Δ₀`, `1Δ₁` of `sumTok`; what remains is a sub-family, and
consistency is inherited (cross-tag intersections are empty, hence not `sumTok`-neighbourhoods). -/

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-! ## (4) `𝒟 ⊴ 𝒟 ⊕ ℰ` — left-injection projection pair

Unlike the product, the coalesced sum *identifies* the two bottoms, so the embedding of `𝒟` must
send `⊥_𝒟 = Δ₀` to the shared bottom `sumTokMaster` and a proper `X` to its left copy `0X`. We
package this in `leftN X` (`= 0X` for proper `X`, `= sumTokMaster` for `X = Δ₀`).

Distinguishing the two cases is exactly the test `X = Δ₀`, which is undecidable for an arbitrary
neighbourhood; consequently the single lemma `oplus_mem_leftN` — and only it — uses `Classical.em`.
This is genuinely unavoidable at this level of generality (Scott's tokens are concrete and decidable,
but we work over arbitrary `NeighborhoodSystem`s), so `inl_trianglelefteq_oplus` depends on
`Classical.choice` (called out in the axiom audit). Every other part of Exercise 6.27 is choice-free. -/


theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/-- **Exercise 6.27 (4).** `𝒟 ⊴ 𝒟 ⊕ ℰ`. (Uses `Classical.choice` via `oplus_mem_leftN`.) -/
theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

/-! ## (5) `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` — the strict maps embed in all maps

A strict map *is* an approximable map, so `𝒟 →⊥ ℰ` sits inside `𝒟 → ℰ` by inclusion `i`, with the
*strictification* `j` (force `f(⊥) = ⊥`) as its retraction. `strictify f ⊑ f` always, and on a strict
`f` strictification is the identity; this gives the projection-pair laws `j ∘ i = id`,
`i ∘ j ⊑ id`. We work over **arbitrary** systems `V₀, V₁` (not just `Str`); the construction is
choice-free. We realise `i, j` on principal inputs via `ofMono` of the element-level inclusion /
strictification, then identify their element maps using the representations `funSpaceEquiv`
(`|𝒟→ℰ| ≃ ApproximableMap`) and `strictFunEquiv` (`|𝒟→⊥ℰ| ≃ StrictMap`). -/

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


end Part5

/-! ## (6) `𝒟 ⊴ 𝒟 ⊗ ℰ` is **false** in general

The smash product sends `(x, ⊥)` and `(⊥, y)` to the single bottom, so if `ℰ` contributes no proper
neighbourhood the whole product collapses to its bottom. Concretely, for the one-point unit `ℰ = 𝟙`
the system `𝒟 ⊗ 𝟙` has *only* its master as a neighbourhood, hence a one-point element lattice; a
`𝒟` with two distinct points therefore cannot embed. This refutes the universal claim. -/


end Exercise627
end DomainTheory.NeighbourhoodSystems
