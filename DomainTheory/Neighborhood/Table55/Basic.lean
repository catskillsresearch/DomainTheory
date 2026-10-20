/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem41

@[expose] public section

/-!
# Lecture V (§5) — Table 5.5: a table of combinators

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture V,
*Typed λ-calculus*. Table 5.5 summarizes how the standard combinators are defined by `λ`-notation.
In the neighbourhood-system/approximable-map framework of these lectures, each combinator scheme is
realized as a concrete **approximable map**, and Scott's `λ`-equations become the *value equations*
of those maps (proved through the projection/pairing/`eval`/`curry`/`fix` API of Lecture III–IV).

| Scott's table | here | value equation |
| ------------- | ---- | -------------- |
| `P₀ = λx,y.x` | `P₀ = proj₀` | `P₀⟨x,y⟩ = x` |
| `P₁ = λx,y.y` | `P₁ = proj₁` | `P₁⟨x,y⟩ = y` |
| `pair = λx λy.⟨x,y⟩` | `pairC = curry I` | `pairC x y = ⟨x,y⟩` |
| `diag = λx.⟨x,x⟩` | `diag = ⟨I,I⟩` | `diag x = ⟨x,x⟩` |
| `funpair = λf λg λx.⟨f x, g x⟩` | `funpairC` | `funpairC f g x = ⟨f x, g x⟩` |
| `proj_i^n` | base cases `P₀,P₁` | (scheme; see note) |
| `inv_{i,j}^n` | base case `swapC` | `swapC⟨x,y⟩ = ⟨y,x⟩` |
| `eval = λf,x.f x` | `evalC = evalMap` | `evalC⟨f,x⟩ = f x` |
| `curry = λg λx λy.g(x,y)` | `curryC = ofIso` | `curryC g x y = g⟨x,y⟩` |
| `comp = λg,f λx.g(f x)` | `compC = curry …` | `compC⟨g,f⟩ = g ∘ f` |
| `const = λk λx.k` | `constC = curry proj₀` | `constC k x = k` |
| `fix = λf !x.f x` | `fixC = fixMap` | `fixC f = fix f` |

**A note on `n`-ary schemes.** Scott stresses that the table entries are *schemes*: `n`-tuple,
`proj_i^n`, `inv_{i,j}^n` are families parameterized by an arity `n`. The framework models the
`n`-fold product by *iterating* the binary product `prod`, so the `n`-ary combinators are obtained
by iterating the binary ones recorded here (`P₀`/`P₁` are `proj_0^2`/`proj_1^2`; `pairC` is the
`2`-tuple; `swapC` is `inv_{0,1}^2`). We give the binary base cases as concrete maps.

All combinators are **data**; the genuinely first-order ones (`P₀`, `P₁`, `pairC`, `diag`,
`funpairC`, `swapC`, `evalC`, `constC`, `compC`) are *choice-free*
(`#print axioms ⊆ {propext, Quot.sound}`). `curryC` and `fixC` are built from the established
`ofIso`/`fixMap` API.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-! ### `P₀ = λx,y.x` and `P₁ = λx,y.y` — the binary projections. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `P₀ = λx,y.x`, the first projection `𝒟₀ × 𝒟₁ → 𝒟₀`. -/
def P₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₀ :=
  proj₀ V₀ V₁

/-- **Table 5.5 (Scott 1981, PRG-19).** `P₁ = λx,y.y`, the second projection `𝒟₀ × 𝒟₁ → 𝒟₁`. -/
def P₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₁ :=
  proj₁ V₀ V₁

@[simp] theorem P₀_apply (x : V₀.Element) (y : V₁.Element) :
    (P₀ V₀ V₁).toElementMap (pair x y) = x := by
  rw [P₀, toElementMap_proj₀, fst_pair]

@[simp] theorem P₁_apply (x : V₀.Element) (y : V₁.Element) :
    (P₁ V₀ V₁).toElementMap (pair x y) = y := by
  rw [P₁, toElementMap_proj₁, snd_pair]

/-! ### `pair = λx λy.⟨x,y⟩` — the curried element pairing. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `pair = λx λy.⟨x,y⟩`, as the curried map
`𝒟₀ → (𝒟₁ → 𝒟₀ × 𝒟₁)`. -/
def pairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (funSpace V₁ (prod V₀ V₁)) := curry (idMap (prod V₀ V₁))

/-! ### `diag = λx.⟨x,x⟩` — the diagonal. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `diag = λx.⟨x,x⟩`, the diagonal `𝒟 → 𝒟 × 𝒟`. -/
def diagC (V : NeighborhoodSystem α) : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

@[simp] theorem diagC_apply (x : V.Element) : (diagC V).toElementMap x = pair x x := by
  rw [diagC, toElementMap_paired, toElementMap_idMap]

/-! ### `inv = λx,y.⟨y,x⟩` — the binary argument swap (base case of `inv_{i,j}^n`). -/

/-- **Table 5.5 (Scott 1981, PRG-19).** The base case `inv_{0,1}^2 = λx,y.⟨y,x⟩` of the
argument-swap scheme: `𝒟₀ × 𝒟₁ → 𝒟₁ × 𝒟₀`. -/
def swapC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) (prod V₁ V₀) := paired (proj₁ V₀ V₁) (proj₀ V₀ V₁)

@[simp] theorem swapC_apply (x : V₀.Element) (y : V₁.Element) :
    (swapC V₀ V₁).toElementMap (pair x y) = pair y x := by
  rw [swapC, toElementMap_paired, toElementMap_proj₁, toElementMap_proj₀, snd_pair, fst_pair]

/-! ### `eval = λf,x.f x` — evaluation. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `eval = λf,x.f(x)`, evaluation `(𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁`
(this is Theorem 3.11's `evalMap`). -/
def evalC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V₀ V₁) V₀) V₁ := evalMap V₀ V₁

/-! ### `const = λk λx.k` — the constant-function combinator. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `const = λk λx.k`, sending `k ∈ |𝒟₁|` to the constant map
`𝒟₀ → 𝒟₁`. Realized as `curry(p₀)`. -/
def constC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₁ (funSpace V₀ V₁) := curry (proj₀ V₁ V₀)

/-! ### `curry = λg λx λy.g(x,y)` — currying as a combinator. -/

/-- The order-isomorphism `|𝒟₀ × 𝒟₁ → 𝒟₂| ≃o |𝒟₀ → (𝒟₁ → 𝒟₂)|` between the *function-space
domains*, obtained from Theorem 3.10 (`funSpaceEquiv`) and Theorem 3.12 (`curryEquiv`). -/
def curryIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (funSpace (prod V₀ V₁) V₂).Element ≃o (funSpace V₀ (funSpace V₁ V₂)).Element :=
  (funSpaceEquiv (prod V₀ V₁) V₂).trans
    ((curryEquiv V₀ V₁ V₂).trans (funSpaceEquiv V₀ (funSpace V₁ V₂)).symm)

/-- **Table 5.5 (Scott 1981, PRG-19).** `curry = λg λx λy.g(x,y)` as an approximable map
`(𝒟₀ × 𝒟₁ → 𝒟₂) → (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
def curryC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace (prod V₀ V₁) V₂) (funSpace V₀ (funSpace V₁ V₂)) :=
  ofIso (curryIso V₀ V₁ V₂)

/-! ### `comp = λg,f λx.g(f x)` — composition as a combinator. -/

/-- The uncurried `(g, f), x ↦ g(f(x))` over `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, built purely from
projections, pairing and `eval` (this is the variable-free expression Scott alludes to). -/
def compMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

/-- **Table 5.5 (Scott 1981, PRG-19).** `comp = λg,f λx.g(f(x))` as an approximable map
`((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) → (𝒟₀ → 𝒟₂)`. -/
def compC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compMapTbl V₀ V₁ V₂)

/-! ### `funpair = λf λg λx.⟨f x, g x⟩`. -/

/-- The uncurried `(f, g), x ↦ ⟨f(x), g(x)⟩` over `((𝒟₂→𝒟₀) × (𝒟₂→𝒟₁)) × 𝒟₂ → 𝒟₀ × 𝒟₁`. -/
def funpairMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂) (prod V₀ V₁) :=
  paired
    ((evalMap V₂ V₀).comp
      (paired
        ((proj₀ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))
    ((evalMap V₂ V₁).comp
      (paired
        ((proj₁ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))

/-- **Table 5.5 (Scott 1981, PRG-19).** `funpair = λf λg λx.⟨f(x), g(x)⟩`, the curried operation
`(𝒟₂→𝒟₀) → ((𝒟₂→𝒟₁) → (𝒟₂ → 𝒟₀ × 𝒟₁))`. -/
def funpairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace V₂ V₀)
      (funSpace (funSpace V₂ V₁) (funSpace V₂ (prod V₀ V₁))) :=
  curry (curry (funpairMapTbl V₀ V₁ V₂))

/-! ### `fix = λf !x.f x` — the least fixed-point operator. -/

/-- **Table 5.5 (Scott 1981, PRG-19).** `fix = λf.!x.f(x)`, the least fixed-point operator
`(𝒟 → 𝒟) → 𝒟` (Theorem 4.2's `fixMap`). -/
def fixC (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V := fixMap V
end DomainTheory.Neighborhood
