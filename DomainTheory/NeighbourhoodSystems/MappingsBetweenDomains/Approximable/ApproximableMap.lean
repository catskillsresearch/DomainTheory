/-ai
An approximable map between neighbourhood systems is a relation on sets such that related sets are neighbourhoods, the two master neighbourhoods are related, an input related to two outputs is related to their intersection, and the relation persists when the input is replaced by a smaller neighbourhood and the output by a larger neighbourhood.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- **Definition 2.1 (Scott 1981, PRG-19).** An *approximable mapping* `f : 𝒟₀ → 𝒟₁` is a relation
`rel` between neighbourhoods (`rel X Y`, Scott's `X f Y`) confined to `𝒟₀ × 𝒟₁` and satisfying
Scott's three conditions:

* (i)   `Δ₀ f Δ₁`                                   — `master_rel`;
* (ii)  `X f Y` and `X f Y'` imply `X f (Y ∩ Y')`   — `inter_right`;
* (iii) `X f Y`, `X' ⊆ X`, `Y ⊆ Y'` imply `X' f Y'` — `mono` (the targets `X'`, `Y'` must be
  neighbourhoods, as Scott's relation lives on `𝒟₀ × 𝒟₁`). -/
structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where
  /-- The underlying neighbourhood relation `X f Y`. -/
  rel : Set α → Set β → Prop
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (domain side): related inputs are neighbourhoods. -/
  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (codomain side): related outputs are neighbourhoods. -/
  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y
  /-- (i) `Δ₀ f Δ₁`. -/
  master_rel : rel V₀.master V₁.master
  /-- (ii) intersectivity on the output: `X f Y → X f Y' → X f (Y ∩ Y')`. -/
  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')
  /-- (iii) monotonicity: a sharper input `X' ⊆ X` with a blunter output `Y ⊆ Y'` is still related,
  provided `X'`, `Y'` are neighbourhoods. -/
  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

end DomainTheory.NeighbourhoodSystems
