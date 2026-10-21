/-ai
This file gathers and re-exports the combinators of Table 5.5 (Scott 1981, PRG-19), each realized as an approximable map: the two binary projections, curried pairing, the diagonal, argument swap, evaluation, the constant combinator, the curry isomorphism and the curry combinator, the uncurried composition body and the composition combinator, the uncurried function-pairing body and the function-pairing combinator, and the least-fixed-point combinator, together with the value equations for the projections, the diagonal, and the swap.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.pairC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.evalC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.constC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryIso
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compMapTbl
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairMapTbl
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.fixC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply

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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-! ### `P₀ = λx,y.x` and `P₁ = λx,y.y` — the binary projections. -/


/-! ### `pair = λx λy.⟨x,y⟩` — the curried element pairing. -/


/-! ### `diag = λx.⟨x,x⟩` — the diagonal. -/


/-! ### `inv = λx,y.⟨y,x⟩` — the binary argument swap (base case of `inv_{i,j}^n`). -/


/-! ### `eval = λf,x.f x` — evaluation. -/


/-! ### `const = λk λx.k` — the constant-function combinator. -/


/-! ### `curry = λg λx λy.g(x,y)` — currying as a combinator. -/


/-! ### `comp = λg,f λx.g(f x)` — composition as a combinator. -/


/-! ### `funpair = λf λg λx.⟨f x, g x⟩`. -/


/-! ### `fix = λf !x.f x` — the least fixed-point operator. -/

end DomainTheory.NeighbourhoodSystems
