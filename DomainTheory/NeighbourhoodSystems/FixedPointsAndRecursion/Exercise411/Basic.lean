/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410

@[expose] public section

/-!
# Exercise 4.11 (Scott 1981, PRG-19, Lecture IV) — Plotkin's uniqueness of `fix`

(Suggested by G. Plotkin.) Regard `fix` as assigning a fixed-point operator `F_𝒟 : (𝒟 → 𝒟) → 𝒟`
to each domain `𝒟`. Scott asks to show `fix` is the **unique** such assignment `𝒟 ↝ F_𝒟` subject to:

* (i)   `F_𝒟 : (𝒟 → 𝒟) → 𝒟`;
* (ii)  `F_𝒟(f) = f(F_𝒟(f))` for all `f : 𝒟 → 𝒟`  (each value is a fixed point);
* (iii) *(uniformity)* whenever `f₀ : 𝒟₀ → 𝒟₀`, `f₁ : 𝒟₁ → 𝒟₁` and `h : 𝒟₀ → 𝒟₁` satisfy
        `h(⊥) = ⊥` and `h ∘ f₀ = f₁ ∘ h`, then `h(F_{𝒟₀}(f₀)) = F_{𝒟₁}(f₁)`.

**`fix` satisfies (iii)** (`fixElement_uniform`): writing `fix(f₀) = ⊔ₙ f₀ⁿ(⊥)` (Theorem 4.2(iii)),
the intertwining `h ∘ f₀ = f₁ ∘ h` together with `h(⊥) = ⊥` gives `h(f₀ⁿ(⊥)) = f₁ⁿ(⊥)` by induction,
and `h` preserves directed unions, so `h(fix f₀) = ⊔ₙ f₁ⁿ(⊥) = fix f₁`.

**Uniqueness** (`fix_unique_of_uniform`): given *any* `F` obeying (ii) and (iii), and any `f : 𝒟 → 𝒟`,
apply (iii) with the inclusion `h = ι : 𝒟_{fix f} ↪ 𝒟` of the relativized domain (Exercise 4.10).
`ι(⊥) = ⊥` (`inclMap_bot`) and `ι ∘ f' = f ∘ ι` (`inclMap_intertwine`, from
`relMap_toElementMap_embed`). Hence `ι(F_{𝒟_{fix f}}(f')) = F_𝒟(f)`. But `F_{𝒟_{fix f}}(f')` is a
fixed point of `f'` by (ii), and `f'` has **exactly one** fixed point (Exercise 4.10,
`relMap_unique_fixed`) — the top point `fix f` — so the left side is `ι(fix f) = fix f`. Therefore
`F_𝒟(f) = fix f`.

`fix` satisfying (i)/(ii) is Theorem 4.2 (`fixMap`, `fixMap_fixed`). The uniqueness proof uses only
the project's permitted `Element.ext`; the inclusion data `inclMap` is **choice-free**.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### `fix` satisfies the uniformity condition (iii). -/

/-! ### The inclusion `ι : 𝒟ₐ ↪ 𝒟` of the relativized domain (Exercise 4.10). -/

/-- The inclusion `𝒟ₐ → 𝒟` as an approximable map: an `a`-neighbourhood `X` relates to any larger
`𝒟`-neighbourhood `Y ⊇ X`. Its elementwise action is `embed a` (`inclMap_toElementMap`). -/
def inclMap (a : V.Element) : ApproximableMap (relSystem a) V where
  rel X Y := a.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom := fun h => h.1
  rel_cod := fun h => h.2.1
  master_rel := ⟨a.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hVY, hXY⟩ ⟨_, hVY', hXY'⟩
    exact ⟨haX, V.inter_mem hVY hVY' (a.sub haX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' haX' hVY'
    exact ⟨haX', hVY', (hX'X.trans hXY).trans hYY'⟩

end ApproximableMap

/-! ### Plotkin's uniqueness theorem. -/

open ApproximableMap

universe u
end DomainTheory.NeighbourhoodSystems
