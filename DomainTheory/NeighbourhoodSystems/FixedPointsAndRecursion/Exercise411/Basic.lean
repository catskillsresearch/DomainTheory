/-ai
This file gathers and re-exports Exercises 4.7 and 4.10 together with the inclusion of a relativized domain into the original domain, as the setting for Plotkin's uniqueness of the fixed-point operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap

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


end ApproximableMap

/-! ### Plotkin's uniqueness theorem. -/

open ApproximableMap

end DomainTheory.NeighbourhoodSystems
