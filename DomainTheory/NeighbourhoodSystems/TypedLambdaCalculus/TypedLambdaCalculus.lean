module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.DomainConstructs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.FixedPointsAndRecursion
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.MappingsBetweenDomains
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Computability.PartrecBasis
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Tactic.Ring

@[expose] public section

section
/- concordance: source L3005 EXERCISE 5.7 currying the lambda notation -/
/- concordance: source L3003 EXERCISES — Lecture V exercises -/
-- Exercise507/curry₃.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

/-- **Three-variable abstraction** `λx, y, z. τ`, via nested currying on `(D₀ × D₁) × D₂ → D₃`.
Each `curry` strips one variable, so a function of `n` variables is reached by `n - 1` curryings —
single-variable binders all the way down. -/
def curry₃ (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) :
    ApproximableMap V₀ (funSpace V₁ (funSpace V₂ V₃)) :=
  curry (curry g)

end DomainTheory.NeighbourhoodSystems.Exercise507
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise507
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The combinator `σ(x, y)` (apply `σ : D₀ × D₁ → D₂` to two arguments) is expressed through the
*one-variable* curried form: `σ(⟨x, y⟩) = (curry σ)(x)(y)`. The right-hand side uses only
single-variable application. -/
theorem app_two_args (σ : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    σ.toElementMap (pair x y) =
      (toApproxMap ((curry σ).toElementMap x)).toElementMap y := by
  rw [toElementMap_curry_apply]
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The defining equation of `curry₃`: `(λx, y, z. g)(x)(y)(z) = g⟨⟨x, y⟩, z⟩`. -/
theorem curry₃_apply (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
    (x : V₀.Element) (y : V₁.Element) (z : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
      g.toElementMap (pair (pair x y) z) := by
  rw [curry₃, toElementMap_curry_apply, toElementMap_curry_apply]
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Two-variable abstraction.** `λx, y. τ` is `curry`, characterised by `(curry g)(x)(y) = g⟨x, y⟩`.
It binds one variable `x` and returns the one-variable function `λy. g⟨x, y⟩`. -/
theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Surjective pairing.** Every element `z : D₀ × D₁` is recovered from its projections:
`⟨p₀(z), p₁(z)⟩ = z`. This is what makes `p₀`, `p₁`, `pair` enough to encode the product. -/
theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **One-argument-at-a-time application.** For `h : D₀ → (D₁ → D₂)`, applying the uncurried map to
a `pair` is the same as applying `h` to `x` and then to `y`:
`(uncurry h)(⟨x, y⟩) = h(x)(y)`. -/
theorem uncurry_apply (h : ApproximableMap V₀ (funSpace V₁ V₂))
    (x : V₀.Element) (y : V₁.Element) :
    (uncurry h).toElementMap (pair x y) =
      (toApproxMap (h.toElementMap x)).toElementMap y := by
  rw [uncurry_eq, toElementMap_comp, toElementMap_paired, toElementMap_comp,
    toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The two encodings are mutually inverse: uncurrying the two-variable abstraction returns the
original two-variable function. -/
theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g
end

section
set_option linter.unusedVariables false

theorem example_507.{u_1, u_2, u_5} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {α_1 : Type u_5}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
  (g :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1 (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.uncurry α β α_1 V₀ V₁ V₂
      (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₂ g))
    g :=
  @DomainTheory.NeighbourhoodSystems.Exercise507.uncurry_lam_two_vars
end

end DomainTheory.NeighbourhoodSystems.Exercise507
namespace DomainTheory.NeighbourhoodSystems.Exercise508
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- A *domain*: a token type together with its neighbourhood system. Bundling lets us build an
intrinsically-typed syntax of combinator terms. We work over `Type` (universe `0`), which covers all
the concrete domains of these lectures (`N`, `T`, `C`, …) and their products/function spaces. -/
structure Dom where
  /-- The token type. -/
  carrier : Type
  /-- The neighbourhood system on `carrier`. -/
  sys : NeighborhoodSystem carrier

/-- The function domain `(A → B)`; its carrier is `ApproximableMap A.sys B.sys` and its system is the
function space `funSpace A.sys B.sys`. -/
abbrev Dom.arrow (A B : Dom) : Dom := ⟨ApproximableMap A.sys B.sys, funSpace A.sys B.sys⟩
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `CL A`: a **variable-free** combinator expression of type `A`. The only constructors are
constants and application, so application (`σ(τ)`) is the sole mode of combination. -/
inductive CL : Dom → Type 1 where
  | con {A : Dom} (c : A.sys.Element) : CL A
  | app {A B : Dom} (f : CL (A.arrow B)) (a : CL A) : CL B


/-- The denotation of a variable-free combinator expression: a single element. -/
def CL.denote : {A : Dom} → CL A → A.sys.Element
  | _, .con c => c
  | _, .app f a => (toApproxMap f.denote).toElementMap a.denote
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `Poly X A`: an open term of type `A` with a single free variable of type `X`. Constructors:
the variable, a closed constant (any element of any domain — "enough combinators available"), and
application. This is the syntax of `λ`-bodies whose abstraction we want to eliminate. -/
inductive Poly (X : Dom) : Dom → Type 1 where
  | var : Poly X X
  | con {A : Dom} (c : A.sys.Element) : Poly X A
  | app {A B : Dom} (f : Poly X (A.arrow B)) (a : Poly X A) : Poly X B


/-- The denotation of an open term: the body as a function of its free variable. -/
def Poly.denote {X : Dom} : {A : Dom} → Poly X A → X.sys.Element → A.sys.Element
  | _, .var, x => x
  | _, .con c, _ => c
  | _, .app f a, x => (toApproxMap (f.denote x)).toElementMap (a.denote x)
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `I = λx.x` as an element of `(X → X)`. -/
def Ielem (X : Dom) : (X.arrow X).sys.Element := toFilter (idMap X.sys)
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `K = λx, y.x` as an element of `(A → (X → A))`. -/
def Kelem (A X : Dom) : (A.arrow (X.arrow A)).sys.Element := toFilter (curry (proj₀ A.sys X.sys))
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- The uncurried body of `S`: with `F : 𝒟ₓ → (𝒟ₐ → 𝒟_b)`, `G : 𝒟ₓ → 𝒟ₐ`, `x : 𝒟ₓ`,
`Sbody⟨⟨F, G⟩, x⟩ = (F x)(G x)`, expressed using only `proj`, `pair` and `eval`. -/
def Sbody (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap
      (prod (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx) Vb :=
  (evalMap Va Vb).comp
    (paired
      ((evalMap Vx (funSpace Va Vb)).comp
        (paired
          ((proj₀ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx)))
      ((evalMap Vx Va).comp
        (paired
          ((proj₁ (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)).comp
            (proj₀ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))
          (proj₁ (prod (funSpace Vx (funSpace Va Vb)) (funSpace Vx Va)) Vx))))
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `S = λf, g, x. f(x)(g(x))`, the curried form
`(𝒟ₓ → (𝒟ₐ → 𝒟_b)) → ((𝒟ₓ → 𝒟ₐ) → (𝒟ₓ → 𝒟_b))`. -/
def Smap (Vx : NeighborhoodSystem αx) (Va : NeighborhoodSystem αa) (Vb : NeighborhoodSystem αb) :
    ApproximableMap (funSpace Vx (funSpace Va Vb))
      (funSpace (funSpace Vx Va) (funSpace Vx Vb)) :=
  curry (curry (Sbody Vx Va Vb))
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `S = λf, g, x. f(x)(g(x))` as an element of
`((X → (A → B)) → ((X → A) → (X → B)))`. -/
def Selem (X A B : Dom) :
    ((X.arrow (A.arrow B)).arrow ((X.arrow A).arrow (X.arrow B))).sys.Element :=
  toFilter (Smap X.sys A.sys B.sys)
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- **Bracket abstraction.** Turn an open body `t` (a `λ`-body with one free variable) into a
*variable-free* combinator expression denoting `λx.t`, using only application and the combinators
`I`, `K`, `S` together with the constants already occurring in `t`:

* `[x] x        = I`
* `[x] c        = K(c)`           (`c` a constant / closed term)
* `[x] (f a)    = S([x]f)([x]a)`.
-/
def bracket {X : Dom} : {A : Dom} → Poly X A → CL (X.arrow A)
  | _, .var => .con (Ielem X)
  | _, .con c => .app (.con (Kelem _ X)) (.con c)
  | _, .app f a => .app (.app (.con (Selem X _ _)) (bracket f)) (bracket a)
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- The defining equation of `S`: `S(F)(G)(x) = F(x)(G(x))`. -/
theorem Smap_apply (F : (funSpace Vx (funSpace Va Vb)).Element) (G : (funSpace Vx Va).Element)
    (x : Vx.Element) :
    (toApproxMap ((toApproxMap ((Smap Vx Va Vb).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Smap, toElementMap_curry_apply, toElementMap_curry_apply]
  simp only [Sbody, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]
end

section
variable {α β γ : Type*}

/-- `toApproxMap ∘ toFilter = id`: the representation of a function-space *element* by an approximable
map is a left inverse of `toFilter` (this is `funSpaceEquiv` unfolded). -/
theorem toApproxMap_toFilter {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) : toApproxMap (toFilter f) = f := by
  have he := (funSpaceEquiv V₀ V₁).apply_symm_apply f
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `I(x) = x`. -/
theorem Ielem_apply (X : Dom) (x : X.sys.Element) :
    (toApproxMap (Ielem X)).toElementMap x = x := by
  rw [Ielem, toApproxMap_toFilter, toElementMap_idMap]
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `K(c)(x) = c`. -/
theorem Kelem_apply (A X : Dom) (c : A.sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap (Kelem A X)).toElementMap c)).toElementMap x = c := by
  rw [Kelem, toApproxMap_toFilter]
  have h := toElementMap_curry_apply (proj₀ A.sys X.sys) c x
  rw [toElementMap_proj₀, fst_pair] at h
  exact h
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/-- `S(F)(G)(x) = F(x)(G(x))`. -/
theorem Selem_apply (X A B : Dom)
    (F : (X.arrow (A.arrow B)).sys.Element) (G : (X.arrow A).sys.Element) (x : X.sys.Element) :
    (toApproxMap ((toApproxMap ((toApproxMap (Selem X A B)).toElementMap F)).toElementMap G)).toElementMap x
      = (toApproxMap ((toApproxMap F).toElementMap x)).toElementMap ((toApproxMap G).toElementMap x) := by
  rw [Selem, toApproxMap_toFilter]
  exact Smap_apply F G x
end

section
variable {α β γ : Type*}
variable {αx αa αb : Type*}
  {Vx : NeighborhoodSystem αx} {Va : NeighborhoodSystem αa} {Vb : NeighborhoodSystem αb}

/- concordance: source L3013 EXERCISE 5.8 combinatory completeness -/
/-- **Combinatory completeness (Exercise 5.8, Scott 1981, PRG-19).** The variable-free combinator
expression `bracket t` denotes exactly the function `λx.t`: applied to any `x`, it yields `t.denote x`.

Thus, with `I`, `K`, `S` (and the constants of `t`) available, every `λ`-abstraction can be defined
by combining combinators using application as the only mode of combination — Scott's "turning of the
tables". -/
theorem bracket_spec {X : Dom} {A : Dom} (t : Poly X A) (x : X.sys.Element) :
    (toApproxMap (bracket t).denote).toElementMap x = t.denote x := by
  induction t with
  | var =>
      simp only [bracket, CL.denote, Poly.denote]
      exact Ielem_apply X x
  | @con A c =>
      simp only [bracket, CL.denote, Poly.denote]
      exact Kelem_apply A X c x
  | @app A B f a ihf iha =>
      simp only [bracket, CL.denote, Poly.denote]
      have hS := Selem_apply X A B (CL.denote (bracket f)) (CL.denote (bracket a)) x
      rw [ihf, iha] at hS
      exact hS
end

section
set_option linter.unusedVariables false

theorem example_508 : ∀ {X A : DomainTheory.NeighbourhoodSystems.Exercise508.Dom} (t : DomainTheory.NeighbourhoodSystems.Exercise508.Poly X A)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element X.carrier X.sys),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element A.carrier A.sys)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap X.carrier A.carrier X.sys A.sys
      (@DomainTheory.NeighbourhoodSystems.toApproxMap X.carrier A.carrier X.sys A.sys
        (@DomainTheory.NeighbourhoodSystems.Exercise508.CL.denote (X.arrow A)
          (@DomainTheory.NeighbourhoodSystems.Exercise508.bracket X A t)))
      x)
    (@DomainTheory.NeighbourhoodSystems.Exercise508.Poly.denote X A t x) :=
  @DomainTheory.NeighbourhoodSystems.Exercise508.bracket_spec
end

end DomainTheory.NeighbourhoodSystems.Exercise508
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Commutation `f ∘ g = g ∘ f` read elementwise: `f(g(x)) = g(f(x))`. -/
theorem commute_apply {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) (x : V.Element) :
    f.toElementMap (g.toElementMap x) = g.toElementMap (f.toElementMap x) := by
  have h1 : (f.comp g).toElementMap x = (g.comp f).toElementMap x := by rw [hcomm]
  rwa [toElementMap_comp, toElementMap_comp] at h1

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/- concordance: source L3015 EXERCISE 5.9 common fixed points -/
/-- **Exercise 5.9 (Scott 1981, PRG-19).** Commuting approximable maps have a *least common fixed
point* `x = f(x) = g(x)`. -/
theorem commuting_least_common_fixed {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) :
    ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
      ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w := by
  set a := f.fixElement with ha_def
  have hfa : f.toElementMap a = a := toElementMap_fixElement f
  -- `a ⊑ g(a)` since `g(a)` is a fixed point of `f`.
  have ha_le : a ≤ g.toElementMap a := by
    apply fixElement_le_of_toElementMap_le f
    rw [commute_apply hcomm, hfa]
  set x := g.fixAbove ha_le with hx_def
  have hgx : g.toElementMap x = x := fixAbove_isFixed g ha_le
  have hax : a ≤ x := le_fixAbove g ha_le
  -- each `gⁿ(a)` is a fixed point of `f`.
  have hfix_each : ∀ n, f.toElementMap (g.iterFrom a n) = g.iterFrom a n := by
    intro n
    induction n with
    | zero => rw [iterFrom_zero]; exact hfa
    | succ k ih =>
      rw [iterFrom_succ g a k, commute_apply hcomm, ih]
  -- so `f(x) = x` by continuity.
  have hfx : f.toElementMap x = x := by
    apply le_antisymm
    · rw [hx_def, fixAbove, toElementMap_iSupDirected]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hfix_each n]
      exact NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n
    · rw [hx_def, fixAbove]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [← hfix_each n]
      exact f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n)
  refine ⟨x, hfx, hgx, ?_⟩
  intro w hfw hgw
  have haw : a ≤ w := fixElement_le_of_toElementMap_le f (le_of_eq hfw)
  exact fixAbove_least g ha_le haw (le_of_eq hgw)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterElem_zero' (f : ApproximableMap V V) : f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `(f²)ⁿ(⊥) = f^{2n}(⊥)`. -/
theorem comp_self_iterElem (f : ApproximableMap V V) (n : ℕ) :
    (f.comp f).iterElem n = f.iterElem (2 * n) := by
  induction n with
  | zero => rw [iterElem_zero', Nat.mul_zero, iterElem_zero']
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [iterElem_succ, ih, toElementMap_comp, h2, iterElem_succ, iterElem_succ]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** If `f, g` commute and `f(⊥) = g(⊥)`, then
`fix(f) = fix(g)`. -/
theorem fixElement_eq_of_commuting_bot {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f)
    (hbot : f.toElementMap V.bot = g.toElementMap V.bot) :
    f.fixElement = g.fixElement := by
  -- `g(fⁿ⊥) = fⁿ⁺¹⊥`.
  have hshift : ∀ n, g.toElementMap (f.iterElem n) = f.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', ← hbot]
    | succ k ih =>
      rw [iterElem_succ, ← commute_apply hcomm, ih]
      exact (iterElem_succ f (k + 1)).symm
  -- `g(fix f) = fix f`.
  have hgfixf : g.toElementMap f.fixElement = f.fixElement := by
    rw [fixElement_eq_iSupDirected f, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift n]
      exact NeighborhoodSystem.le_iSupDirected f.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc f.iterElem n ≤ f.iterElem (n + 1) := iterElem_mono f (Nat.le_succ n)
        _ = g.toElementMap (f.iterElem n) := (hshift n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => g.toElementMap (f.iterElem m)) _ n
  -- symmetric: `f(fix g) = fix g`.
  have hshift' : ∀ n, f.toElementMap (g.iterElem n) = g.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', hbot]
    | succ k ih =>
      rw [iterElem_succ, commute_apply hcomm, ih]
      exact (iterElem_succ g (k + 1)).symm
  have hffixg : f.toElementMap g.fixElement = g.fixElement := by
    rw [fixElement_eq_iSupDirected g, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift' n]
      exact NeighborhoodSystem.le_iSupDirected g.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc g.iterElem n ≤ g.iterElem (n + 1) := iterElem_mono g (Nat.le_succ n)
        _ = f.toElementMap (g.iterElem n) := (hshift' n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => f.toElementMap (g.iterElem m)) _ n
  apply le_antisymm
  · exact fixElement_le_of_toElementMap_le f (le_of_eq hffixg)
  · exact fixElement_le_of_toElementMap_le g (le_of_eq hgfixf)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** In particular `fix(f) = fix(f²)`: the `f²`-chain
`f^{2n}(⊥)` is cofinal in the `f`-chain `fⁿ(⊥)`, so the two least fixed points coincide. -/
theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  · -- `fix f ⊑ fix f²`: `fⁿ⊥ ⊑ f^{2n}⊥ = (f²)ⁿ⊥ ⊑ fix f²`.
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  · -- `fix f² ⊑ fix f`: `fix f` is a fixed point of `f²`.
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_509.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f)))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.commuting_least_common_fixed
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_eq_of_commuting_bot)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_iterTwice
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems.Exercise510
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}

/-- A *proper* product neighbourhood of the smash: `X ∪ Y` with `X ∈ 𝒟₀ ∖ {Δ₀}` and
`Y ∈ 𝒟₁ ∖ {Δ₁}` (both factors strictly below their masters). -/
def SmashProper (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (W : Set (α ⊕ β)) : Prop :=
  ∃ X Y, V₀.mem X ∧ X ≠ V₀.master ∧ V₁.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A neighbourhood that is `⊆ Δ₀` and equals `Δ₀` exactly when it contains `Δ₀`. A proper factor
`X ≠ Δ₀` stays proper after intersecting with anything: `X ∩ X' ≠ Δ₀`. -/
theorem inter_ne_master_left {X X' : Set α} (hX : V₀.mem X) (hXne : X ≠ V₀.master) :
    X ∩ X' ≠ V₀.master := by
  intro h
  apply hXne
  refine Set.Subset.antisymm (V₀.sub_master hX) ?_
  rw [← h]; exact Set.inter_subset_left
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem inter_ne_master_right {Y Y' : Set β} (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) :
    Y ∩ Y' ≠ V₁.master :=
  inter_ne_master_left (V₀ := V₁) hY hYne
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/- concordance: source L3017 EXERCISE 5.10 smash product -/
/-- **Exercise 5.10 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁`.** Neighbourhoods are the
master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` (both factors proper).

*This is a neighbourhood system.* Condition (i) is the master clause. Condition (ii) is the new
content: given two smash neighbourhoods with a consistency witness `Z`,

* if either is the master, the intersection collapses to the other (since `X ⊆ Δ₀`, `Y ⊆ Δ₁`);
* if both are proper, `Z` cannot be the master (that would force a factor to be `Δ₀`/`Δ₁`), so `Z` is
  a *proper* `U ∪ V`; `U ⊆ X ∩ X'` and `V ⊆ Y ∩ Y'` then witness `X ∩ X' ∈ 𝒟₀`, `Y ∩ Y' ∈ 𝒟₁`, both
  still proper (`inter_ne_master_*`). -/
def smash (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hZ hZsub
    · -- W = master
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master hX'),
          Set.inter_eq_right.mpr (V₁.sub_master hY')]
    · -- W = X ∪ Y proper
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
          Set.inter_eq_left.mpr (V₁.sub_master hY)]
      · -- both proper: use the witness Z
        right
        rw [prodNbhd_inter] at hZsub ⊢
        rcases hZ with hZeq | ⟨U, V, hU, _, hV, _, rfl⟩
        · -- Z = master is impossible
          exfalso
          rw [hZeq] at hZsub
          obtain ⟨hΔ₀, _⟩ := prodNbhd_subset_iff.mp hZsub
          exact hXne (Set.Subset.antisymm (V₀.sub_master hX) (hΔ₀.trans Set.inter_subset_left))
        · obtain ⟨hUsub, hVsub⟩ := prodNbhd_subset_iff.mp hZsub
          refine ⟨X ∩ X', Y ∩ Y', ?_, ?_, ?_, ?_, rfl⟩
          · exact V₀.inter_mem hX hX' hU hUsub
          · exact inter_ne_master_left hX hXne
          · exact V₁.inter_mem hY hY' hV hVsub
          · exact inter_ne_master_right hY hYne
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, _, hY, _, rfl⟩)
    · exact subset_rfl
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem smash_master :
    (smash V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem smash_mem_bot {W : Set (α ⊕ β)} :
    (smash V₀ V₁).bot.mem W ↔ W = prodNbhd V₀.master V₁.master := by
  rw [NeighborhoodSystem.mem_bot, smash_master]
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A proper product neighbourhood is a neighbourhood of the smash. -/
theorem smash_mem_proper {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) : (smash V₀ V₁).mem (prodNbhd X Y) :=
  Or.inr ⟨X, Y, hX, hXne, hY, hYne, rfl⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The *strict pairing* `⟨x, y⟩⊗`: the filter generated by the proper product neighbourhoods
`X ∪ Y` with `X ∈ x ∖ {Δ₀}`, `Y ∈ y ∖ {Δ₁}` (plus the master). When either `x` or `y` is `⊥` (i.e.
contains only its master), this collapses to `⊥`. -/
def smashPair (x : V₀.Element) (y : V₁.Element) : (smash V₀ V₁).Element where
  mem W := W = prodNbhd V₀.master V₁.master ∨
    ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩)
    · exact (smash V₀ V₁).master_mem
    · exact smash_mem_proper (x.sub hX) hXne (y.sub hY) hYne
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW'
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        exact ⟨X', Y', hX', hX'ne, hY', hY'ne, by
          rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master (x.sub hX')),
            Set.inter_eq_right.mpr (V₁.sub_master (y.sub hY'))]⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        exact ⟨X, Y, hX, hXne, hY, hYne, by
          rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master (x.sub hX)),
            Set.inter_eq_left.mpr (V₁.sub_master (y.sub hY))]⟩
      · right
        refine ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', inter_ne_master_left (x.sub hX) hXne,
          y.inter_mem hY hY', inter_ne_master_right (y.sub hY) hYne, ?_⟩
        rw [prodNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hsub
    · left
      exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW') hsub
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rfl
      · obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
        right
        exact ⟨X', Y', x.up_mem hX hX' hXX', hX'ne, y.up_mem hY hY' hYY', hY'ne, rfl⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_smashPair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (smashPair x y).mem W ↔ W = prodNbhd V₀.master V₁.master ∨
      ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **A map is *strict* when `f(⊥) = ⊥`.** Relationally: `f` sends the master input only to the master
output. -/
def IsStrict (f : ApproximableMap V₀ V₁) : Prop :=
  ∀ ⦃Y⦄, f.rel V₀.master Y → Y = V₁.master
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict maps `𝒟₀ →⊥ 𝒟₁`, as a subtype carrying the inherited approximation order. -/
abbrev StrictMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :=
  {f : ApproximableMap V₀ V₁ // IsStrict f}
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem eq_bot_of_no_proper {x : V₀.Element} (hx : ∀ X, x.mem X → X = V₀.master) :
    x = V₀.bot :=
  le_antisymm (fun W hW => by rw [NeighborhoodSystem.mem_bot]; exact hx W hW)
    (V₀.bot_le x)
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- An element is `⊥` iff every neighbourhood it contains is the master: `x ≠ ⊥` exactly when `x`
contains a *proper* neighbourhood. -/
theorem exists_proper_of_ne_bot {x : V₀.Element} (hx : x ≠ V₀.bot) :
    ∃ X, x.mem X ∧ X ≠ V₀.master := by
  by_contra hc
  refine hx (le_antisymm (fun W hW => ?_) (V₀.bot_le x))
  rw [NeighborhoodSystem.mem_bot]
  by_contra hWne
  exact hc ⟨W, hW, hWne⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The constant map at `⊥` is strict. -/
theorem isStrict_constBot : IsStrict (constMap V₀ (V₁.bot)) := by
  rintro Y ⟨_, hY⟩
  rwa [NeighborhoodSystem.mem_bot] at hY
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Strictness is exactly `f(⊥) = ⊥`. -/
theorem isStrict_iff_apply_bot {f : ApproximableMap V₀ V₁} :
    IsStrict f ↔ f.toElementMap V₀.bot = V₁.bot := by
  constructor
  · intro h
    apply Element.ext
    intro Y
    rw [NeighborhoodSystem.mem_bot]
    constructor
    · rintro ⟨X, hX, hrel⟩
      rw [NeighborhoodSystem.mem_bot] at hX; subst hX
      exact h hrel
    · rintro rfl
      exact ⟨V₀.master, V₀.bot.master_mem, f.master_rel⟩
  · intro h Y hrel
    have : (f.toElementMap V₀.bot).mem Y := ⟨V₀.master, V₀.bot.master_mem, hrel⟩
    rw [h, NeighborhoodSystem.mem_bot] at this
    exact this
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Strictness is downward closed: a map below a strict map is strict. -/
theorem IsStrict.mono {f g : ApproximableMap V₀ V₁} (hf : IsStrict f) (hgf : g ≤ f) : IsStrict g :=
  fun _ hrel => hf (hgf _ _ hrel)
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The principal filter of the master is `⊥`. -/
theorem principal_master_eq_bot {X : Set α} (hX : V₀.mem X) (hXm : X = V₀.master) :
    V₀.principal hX = V₀.bot := by
  subst hXm; rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A `⊥` left factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_left (y : V₁.Element) : smashPair V₀.bot y = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hxX; exact absurd hxX hXne
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A `⊥` right factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_right (x : V₀.Element) : smashPair x V₁.bot = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hyY; exact absurd hyY hYne
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict pairing is `⊥` iff one of the components is `⊥`: the smash glues `(⊥, y)` and `(x, ⊥)`
to a single bottom. -/
theorem smashPair_eq_bot_iff {x : V₀.Element} {y : V₁.Element} :
    smashPair x y = (smash V₀ V₁).bot ↔ x = V₀.bot ∨ y = V₁.bot := by
  constructor
  · intro h
    by_contra hcon
    obtain ⟨hx, hy⟩ := not_or.mp hcon
    obtain ⟨X, hxX, hXne⟩ := exists_proper_of_ne_bot hx
    obtain ⟨Y, hyY, hYne⟩ := exists_proper_of_ne_bot hy
    -- `prodNbhd X Y` is a proper member of `smashPair x y`, but `⊥` contains only the master.
    have hmem : (smashPair x y).mem (prodNbhd X Y) :=
      Or.inr ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩
    rw [h, smash_mem_bot] at hmem
    obtain ⟨hX, _⟩ := prodNbhd_injective hmem
    exact hXne hX
  · intro h
    apply eq_bot_of_no_proper
    rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
    · rfl
    · exfalso
      rcases h with hx | hy
      · rw [hx, NeighborhoodSystem.mem_bot] at hxX; exact hXne hxX
      · rw [hy, NeighborhoodSystem.mem_bot] at hyY; exact hYne hyY
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The strict pairing is monotone in both arguments. -/
theorem smashPair_mono {x x' : V₀.Element} {y y' : V₁.Element} (hx : x ≤ x') (hy : y ≤ y') :
    smashPair x y ≤ smashPair x' y' := by
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, Y, hx X hxX, hXne, hy Y hyY, hYne, rfl⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A step set among strict maps: `[X, Y] = {f strict ∣ X f Y}`. -/
def sstep (X : Set α) (Y : Set β) : Set (StrictMap V₀ V₁) := {f | f.1.rel X Y}
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_sstep {X : Set α} {Y : Set β} {f : StrictMap V₀ V₁} :
    f ∈ sstep X Y ↔ f.1.rel X Y := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A finite intersection of strict step sets. -/
def sstepFun (L : List (Set α × Set β)) : Set (StrictMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.1.rel p.1 p.2}
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_sstepFun {L : List (Set α × Set β)} {f : StrictMap V₀ V₁} :
    f ∈ sstepFun L ↔ ∀ p ∈ L, f.1.rel p.1 p.2 := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem sstepFun_nil : (sstepFun [] : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simp
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_append (L L' : List (Set α × Set β)) :
    (sstepFun (L ++ L') : Set (StrictMap V₀ V₁)) = sstepFun L ∩ sstepFun L' := by
  ext f
  simp only [mem_sstepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (sstepFun (p :: L) : Set (StrictMap V₀ V₁)) = sstep p.1 p.2 ∩ sstepFun L := by
  ext f
  simp only [mem_sstepFun, List.mem_cons, Set.mem_inter_iff, mem_sstep]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_singleton (X : Set α) (Y : Set β) :
    (sstepFun [(X, Y)] : Set (StrictMap V₀ V₁)) = sstep X Y := by
  rw [sstepFun_cons, sstepFun_nil, Set.inter_univ]
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem sstep_master_eq :
    (sstep V₀.master V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.1.master_rel
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstep_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (sstep X Y ∩ sstep X Y' : Set (StrictMap V₀ V₁)) = sstep X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_sstep]
  constructor
  · rintro ⟨h, h'⟩; exact f.1.inter_right h h'
  · intro h
    exact ⟨f.1.mono h subset_rfl Set.inter_subset_left (f.1.rel_dom h) hY,
           f.1.mono h subset_rfl Set.inter_subset_right (f.1.rel_dom h) hY'⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstep_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (sstep X Y : Set (StrictMap V₀ V₁)) ⊆ sstep X' Y' := by
  intro f hf
  exact f.1.mono hf hX'X hYY' hX' hY'
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 5.10 — the strict function space `(𝒟₀ →⊥ 𝒟₁)`.** Tokens are the strict approximable
maps; neighbourhoods are non-empty finite intersections of step sets. -/
def strictFun (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (StrictMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨⟨constMap V₀ V₁.bot, isStrict_constBot⟩, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, sstepFun_nil.symm⟩,
    ⟨⟨constMap V₀ V₁.bot, isStrict_constBot⟩, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem strictFun_master : (strictFun V₀ V₁).master = Set.univ := rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstepFun_up_closed {L : List (Set α × Set β)} {f f' : StrictMap V₀ V₁}
    (hf : f ∈ sstepFun L) (hff' : f ≤ f') : f' ∈ sstepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A step set is a neighbourhood as soon as it has a (strict) witness. -/
theorem sstep_mem_of_mem {g : StrictMap V₀ V₁} {X : Set α} {Y : Set β} (h : g.1.rel X Y) :
    (strictFun V₀ V₁).mem (sstep X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (sstepFun_singleton X Y).symm⟩, ⟨g, h⟩⟩
  intro p hp; rw [List.mem_singleton] at hp; subst hp
  exact ⟨g.1.rel_dom h, g.1.rel_cod h⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The generation lemma: a filter contains `sstepFun L` iff it contains each step `[Xᵢ, Yᵢ]`. -/
theorem mem_sstepFun_iff (φ : (strictFun V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (sstepFun L) ↔ ∀ p ∈ L, φ.mem (sstep p.1 p.2) := by
  induction L with
  | nil => simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [sstepFun_cons]
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨g, hg⟩ := (φ.sub hmem).2
      have hstep : φ.mem (sstep p.1 p.2) :=
        φ.up_mem hmem (sstep_mem_of_mem (g := g) (hg.1)) Set.inter_subset_left
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (sstepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strictFun_mem_iff {W : Set (StrictMap V₀ V₁)} :
    (strictFun V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
        ∧ W.Nonempty := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Intersection of two neighbourhoods, when non-empty, is again one. -/
theorem strictFun_mem_inter {W W' : Set (StrictMap V₀ V₁)}
    (hW : (strictFun V₀ V₁).mem W) (hW' : (strictFun V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (strictFun V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem strictFun_mem_up_closed {W : Set (StrictMap V₀ V₁)} (hW : (strictFun V₀ V₁).mem W)
    {f f' : StrictMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact sstepFun_up_closed hf hff'
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **The strict map represented by a filter.** `X (toStrictMap φ) Y ↔ [X, Y] ∈ φ`. It is *strict*
because the step `[Δ₀, Y]` with `Y ≠ Δ₁` is empty (no strict map relates `Δ₀` to a proper output),
hence not a neighbourhood, so it cannot belong to `φ`. -/
def toStrictMap (φ : (strictFun V₀ V₁).Element) : StrictMap V₀ V₁ :=
  ⟨{ rel := fun X Y => φ.mem (sstep X Y)
     rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_dom hf
     rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_cod hf
     master_rel := by
       show φ.mem (sstep V₀.master V₁.master); rw [sstep_master_eq]; exact φ.master_mem
     inter_right := by
       intro X Y Y' h h'
       obtain ⟨f, hf⟩ := (φ.sub h).2
       obtain ⟨f', hf'⟩ := (φ.sub h').2
       have hY : V₁.mem Y := f.1.rel_cod hf
       have hY' : V₁.mem Y' := f'.1.rel_cod hf'
       show φ.mem (sstep X (Y ∩ Y'))
       rw [← sstep_inter_right hY hY']
       exact φ.inter_mem h h'
     mono := by
       intro X X' Y Y' h hX'X hYY' hX' hY'
       obtain ⟨g, hg⟩ := (φ.sub h).2
       have hg' : g.1.rel X' Y' := g.1.mono hg hX'X hYY' hX' hY'
       show φ.mem (sstep X' Y')
       exact φ.up_mem h (sstep_mem_of_mem (g := g) hg') (sstep_subset hX' hY' hX'X hYY') },
   by
     intro Y h
     obtain ⟨g, hg⟩ := (φ.sub h).2
     exact g.2 hg⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem toStrictMap_rel {φ : (strictFun V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toStrictMap φ).1.rel X Y ↔ φ.mem (sstep X Y) := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **The filter `f̂ = {F ∣ f ∈ F}` of a strict map.** -/
def toStrictFilter (f : StrictMap V₀ V₁) : (strictFun V₀ V₁).Element where
  mem W := (strictFun V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(strictFun V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    exact ⟨strictFun_mem_inter hW hW' ⟨f, Set.mem_inter hfW hfW'⟩, Set.mem_inter hfW hfW'⟩
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_toStrictFilter {f : StrictMap V₀ V₁} {W : Set (StrictMap V₀ V₁)} :
    (toStrictFilter f).mem W ↔ (strictFun V₀ V₁).mem W ∧ f ∈ W := Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- The generation lemma for maps into the strict function space: `X h (⋂ᵢ[Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_sstepFun_iff (h : ApproximableMap V₀ (strictFun V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (sstepFun L) ↔ ∀ p ∈ L, h.rel X (sstep p.1 p.2) := by
  induction L with
  | nil =>
    simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (strictFun V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [sstepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.rel_cod hmem)).2
      have hstep : h.rel X (sstep p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (sstep_mem_of_mem (g := f) (hf.1))
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (h.rel_cod hmem).2
      have htail : h.rel X (sstepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **The key computation.** For *proper* `X, Y`, `g(⟨↑X, ↑Y⟩⊗)` contains `Z` iff `g` relates the
proper neighbourhood `X ∪ Y` to `Z`. (Coarser members of the strict pairing are absorbed by
monotonicity; the master member needs only that `X ∪ Y ⊆ Δ₀ ∪ Δ₁`.) -/
theorem smashPair_principal_apply (g : ApproximableMap (smash V₀ V₁) V₂)
    {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) {Z : Set γ} :
    (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z
      ↔ g.rel (prodNbhd X Y) Z := by
  constructor
  · rintro ⟨W, hW, hrel⟩
    rcases hW with rfl | ⟨A, B, ⟨_, hXA⟩, _, ⟨_, hYB⟩, _, rfl⟩
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨hXA, hYB⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
  · intro hrel
    exact ⟨prodNbhd X Y, Or.inr ⟨X, Y, ⟨hX, subset_rfl⟩, hXne, ⟨hY, subset_rfl⟩, hYne, rfl⟩, hrel⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- The `X`-section of `g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₂`, as a map `𝒟₁ → 𝒟₂`: `y ↦ g(⟨↑X, y⟩⊗)`. Built with
Exercise 2.8's `ofMono` from its values on principal inputs. -/
def smashSection (g : ApproximableMap (smash V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ :=
  ofMono (fun Y hY => g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY)))
    (by
      intro Y Y' hY hY' hY'Y
      exact toElementMap_mono g (smashPair_mono le_rfl ((V₁.principal_le_iff hY hY').mpr hY'Y)))
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- The section of a *strict* `g` is itself strict: `g(⟨↑X, ⊥⟩⊗) = g(⊥) = ⊥`. -/
theorem isStrict_smashSection {g : ApproximableMap (smash V₀ V₁) V₂} (hg : IsStrict g)
    {X : Set α} (hX : V₀.mem X) : IsStrict (smashSection g hX) := by
  rw [isStrict_iff_apply_bot, smashSection,
    show (V₁.bot) = V₁.principal V₁.master_mem from rfl, toElementMap_ofMono_principal,
    show smashPair (V₀.principal hX) (V₁.principal V₁.master_mem) = (smash V₀ V₁).bot from
      smashPair_bot_right _]
  exact isStrict_iff_apply_bot.mp hg
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- The section is monotone in the neighbourhood `X` (a smaller input gives a larger section). -/
theorem smashSection_mono {g : ApproximableMap (smash V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    smashSection g hX ≤ smashSection g hX' := by
  intro Y Z hrel
  obtain ⟨hY, hmem⟩ := hrel
  exact ⟨hY, toElementMap_mono g
    (smashPair_mono ((V₀.principal_le_iff hX hX').mpr hX'X) le_rfl) Z hmem⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

theorem smashSection_rel {g : ApproximableMap (smash V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} :
    (smashSection g hX).rel Y Z ↔
      ∃ hY : V₁.mem Y, (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z :=
  Iff.rfl
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **Strict curry combinator.** `curry⊥ : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) → (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`, sending `g`
to `x ↦ (y ↦ g(⟨x, y⟩⊗))`. -/
def smashCurryMap (g : StrictMap (smash V₀ V₁) V₂) : StrictMap V₀ (strictFun V₁ V₂) :=
  ⟨{ rel := fun X N => ∃ hX : V₀.mem X, (strictFun V₁ V₂).mem N ∧
       (⟨smashSection g.1 hX, isStrict_smashSection g.2 hX⟩ : StrictMap V₁ V₂) ∈ N
     rel_dom := fun ⟨hX, _⟩ => hX
     rel_cod := fun ⟨_, hN, _⟩ => hN
     master_rel := ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
     inter_right := by
       rintro X N N' ⟨hX, hN, hmem⟩ ⟨_, hN', hmem'⟩
       exact ⟨hX, strictFun_mem_inter hN hN' ⟨_, hmem, hmem'⟩, Set.mem_inter hmem hmem'⟩
     mono := by
       rintro X X' N N' ⟨hX, hN, hmem⟩ hX'X hNN' hX' hN'
       refine ⟨hX', hN', strictFun_mem_up_closed hN' (hNN' hmem) ?_⟩
       exact Subtype.coe_le_coe.mp (smashSection_mono hX hX' hX'X) },
  by
    rintro N ⟨hΔ₀, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    have hall : ∀ p ∈ L, p.2 = V₂.master := by
      intro p hp
      have hpr : (smashSection g.1 hΔ₀).rel p.1 p.2 := hmem p hp
      rw [smashSection_rel] at hpr
      obtain ⟨hp1, hpmem⟩ := hpr
      have hbot : smashPair (V₀.principal hΔ₀) (V₁.principal hp1) = (smash V₀ V₁).bot := by
        rw [principal_master_eq_bot hΔ₀ rfl]; exact smashPair_bot_left _
      rw [hbot, isStrict_iff_apply_bot.mp g.2, NeighborhoodSystem.mem_bot] at hpmem
      exact hpmem
    apply Set.eq_univ_of_forall
    intro f q hq
    rw [hall q hq]
    exact (f.1).rel_master (hL q hq).1⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- Every smash neighbourhood is a product neighbourhood `A ∪ B` (the master is `Δ₀ ∪ Δ₁`). -/
theorem smash_mem_prodNbhd_form {W : Set (α ⊕ β)} (hW : (smash V₀ V₁).mem W) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ W = prodNbhd A B := by
  rcases hW with rfl | ⟨X, Y, hX, _, hY, _, rfl⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, rfl⟩
  · exact ⟨X, Y, hX, hY, rfl⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **Strict uncurry combinator.** `uncurry⊥ : (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) → ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`,
`X ∪ Y (uncurry⊥ h) Z ↔ X h [Y, Z]`. -/
def smashUncurryMap (h : StrictMap V₀ (strictFun V₁ V₂)) : StrictMap (smash V₀ V₁) V₂ :=
  ⟨{ rel := fun W Z => (smash V₀ V₁).mem W ∧ h.1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z)
     rel_dom := fun hh => hh.1
     rel_cod := by
       rintro W Z ⟨_, hrel⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       exact f.1.rel_cod hf
     master_rel := by
       refine ⟨(smash V₀ V₁).master_mem, ?_⟩
       rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
         inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
       exact h.1.master_rel
     inter_right := by
       rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       obtain ⟨f', hf'⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel')).2
       refine ⟨hW, ?_⟩
       rw [← sstep_inter_right (f.1.rel_cod hf) (f'.1.rel_cod hf')]
       exact h.1.inter_right hrel hrel'
     mono := by
       rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
       have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
       have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
       obtain ⟨A, B, hA, hB, rfl⟩ := smash_mem_prodNbhd_form hW₂
       refine ⟨hW₂, ?_⟩
       rw [inl_preimage_prodNbhd] at hinl
       rw [inr_preimage_prodNbhd] at hinr
       rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       have hfB : f.1.rel B Z' := f.1.mono hf hinr hZZ' hB hZ'
       exact h.1.mono hrel hinl (sstep_subset hB hZ' hinr hZZ') hA
         (sstep_mem_of_mem (g := f) hfB) },
   by
     rintro Z ⟨_, hrel⟩
     rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
       inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel
     have huniv : sstep V₁.master Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
     have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep V₁.master Z := by
       rw [huniv]; exact Set.mem_univ _
     obtain ⟨_, hZ⟩ := hcb
     rwa [NeighborhoodSystem.mem_bot] at hZ⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **Roundtrip (i): `uncurry⊥ ∘ curry⊥ = id`.** -/
theorem smashUncurry_curry (g : StrictMap (smash V₀ V₁) V₂) :
    smashUncurryMap (smashCurryMap g) = g := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, hcurry⟩
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hXm, _, hsec⟩ := hcurry
      have hZ : Z = V₂.master := isStrict_smashSection g.2 hXm hsec
      rw [hZ]; exact g.1.master_rel
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hX, _, hY, hmem⟩ := hcurry
      exact (smashPair_principal_apply g.1 hXp hXne hYp hYne).mp hmem
  · intro hrel
    have hW : (smash V₀ V₁).mem W := g.1.rel_dom hrel
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · have hZ : Z = V₂.master := g.2 hrel
      subst hZ
      refine ⟨Or.inl rfl, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
      exact ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
    · refine ⟨smash_mem_proper hXp hXne hYp hYne, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      have hsec : (smashSection g.1 hXp).rel Y Z :=
        ⟨hYp, (smashPair_principal_apply g.1 hXp hXne hYp hYne).mpr hrel⟩
      exact ⟨hXp, sstep_mem_of_mem
        (g := ⟨smashSection g.1 hXp, isStrict_smashSection g.2 hXp⟩) hsec, hsec⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- A step with master codomain is everything: every strict map relates `Y` to `Δ₁`. -/
theorem sstep_cod_master {Y : Set α} (hY : V₀.mem Y) :
    (sstep Y V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_sstep, Set.mem_univ, iff_true]
  exact f.1.mono f.1.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **The decisive computation for the adjunction.** The `X`-section of `uncurry⊥ h` evaluated on a
neighbourhood `Y` is exactly the strict-function value `X h [Y, Z]`. At the boundary (a master
factor) both sides collapse via strictness; off the boundary it is `smashPair_principal_apply`. -/
theorem section_uncurry_rel (h : StrictMap V₀ (strictFun V₁ V₂))
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    (smashSection (smashUncurryMap h).1 hX).rel Y Z ↔ h.1.rel X (sstep Y Z) := by
  rw [smashSection_rel]
  by_cases hXm : X = V₀.master
  · subst hXm
    constructor
    · rintro ⟨hY', hmem⟩
      rw [principal_master_eq_bot hX rfl,
        show smashPair V₀.bot (V₁.principal hY') = (smash V₀ V₁).bot from
          smashPair_eq_bot_iff.mpr (Or.inl rfl),
        isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
      subst hmem
      rw [sstep_cod_master hY]
      exact h.1.rel_master hX
    · intro hrel
      have huniv : sstep Y Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
      have hZ : Z = V₂.master := by
        have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep Y Z := by
          rw [huniv]; exact Set.mem_univ _
        obtain ⟨_, hbz⟩ := hcb
        rwa [NeighborhoodSystem.mem_bot] at hbz
      subst hZ
      exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
  · by_cases hYm : Y = V₁.master
    · subst hYm
      constructor
      · rintro ⟨hY', hmem⟩
        rw [principal_master_eq_bot hY' rfl,
          show smashPair (V₀.principal hX) V₁.bot = (smash V₀ V₁).bot from
            smashPair_eq_bot_iff.mpr (Or.inr rfl),
          isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
        subst hmem
        rw [sstep_master_eq]
        exact h.1.rel_master hX
      · intro hrel
        obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
        have hZ : Z = V₂.master := f.2 hf
        subst hZ
        exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
    · constructor
      · rintro ⟨hY', hmem⟩
        obtain ⟨_, hrel⟩ :=
          (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mp hmem
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel
      · intro hrel
        refine ⟨hY, (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mpr ?_⟩
        refine ⟨smash_mem_proper hX hXm hY hYm, ?_⟩
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **Roundtrip (ii): `curry⊥ ∘ uncurry⊥ = id`.** -/
theorem smashCurry_uncurry (h : StrictMap V₀ (strictFun V₁ V₂)) :
    smashCurryMap (smashUncurryMap h) = h := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro X N
  constructor
  · rintro ⟨hX, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    refine (rel_sstepFun_iff h.1 hX hL).mpr (fun p hp => ?_)
    exact (section_uncurry_rel h hX (hL p hp).1).mp (hmem p hp)
  · intro hrel
    have hX : V₀.mem X := h.1.rel_dom hrel
    have hN : (strictFun V₁ V₂).mem N := h.1.rel_cod hrel
    refine ⟨hX, hN, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    intro p hp
    exact (section_uncurry_rel h hX (hL p hp).1).mpr
      ((rel_sstepFun_iff h.1 hX hL).mp hrel p hp)
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the adjunction.** The strict currying combinator is an
order isomorphism `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃ (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`: the smash product is left adjoint to
the strict function space. -/
def smashCurryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂) where
  toFun := smashCurryMap
  invFun := smashUncurryMap
  left_inv := smashUncurry_curry
  right_inv := smashCurry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (smashCurryMap g).1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z) := by
        have hu : (smashUncurryMap (smashCurryMap g)).1.rel W Z := by
          rw [smashUncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (smashUncurryMap (smashCurryMap g')).1.rel W Z := ⟨g.1.rel_dom hrel, h2⟩
      rw [smashUncurry_curry] at hu'
      exact hu'
    · intro hg X N hrel
      obtain ⟨hX, hN, hmem⟩ := hrel
      refine ⟨hX, hN, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
      intro p hp
      obtain ⟨hY, hmm⟩ := hmem p hp
      obtain ⟨W, hWmem, hWrel⟩ := hmm
      exact ⟨hY, W, hWmem, hg W p.2 hWrel⟩
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 5.10 — the strict function space is complete.** `|𝒟₀ →⊥ 𝒟₁|` is order-isomorphic to
the strict approximable maps `𝒟₀ → 𝒟₁`. -/
def strictFunEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (strictFun V₀ V₁).Element ≃o StrictMap V₀ V₁ where
  toFun := toStrictMap
  invFun := toStrictFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_sstepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨sstep_mem_of_mem (g := f) hf, hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_sstepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_sstepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The identity is strict. -/
theorem isStrict_idMap : IsStrict (idMap V₀) := by
  rintro Y ⟨_, hY, hsub⟩
  exact Set.Subset.antisymm (V₀.sub_master hY) hsub
end

section
set_option linter.unusedVariables false

theorem example_510.{u_1} : ∀ {α : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α V₀ V₀
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀) :=
  @DomainTheory.NeighbourhoodSystems.Exercise510.isStrict_idMap
end

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem smash_mem_iff {W : Set (α ⊕ β)} :
    (smash V₀ V₁).mem W ↔
      W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W := Iff.rfl
end

end DomainTheory.NeighbourhoodSystems.Exercise510
namespace DomainTheory.NeighbourhoodSystems.Exercise511
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `fold : D × D^∞ → D^∞`, the inverse direction of `iterProdIso`. -/
def fold : ApproximableMap (prod V (iterSys V)) (iterSys V) := ofIso (iterProdIso V).symm
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `iterProdIso` reads a stack as its head together with the tail sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `push : D × D^∞ → D^∞`, prepend an element to a stack. -/
def push : ApproximableMap (prod V (iterSys V)) (iterSys V) := fold V
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `unfold : D^∞ → D × D^∞`, the forward direction of `iterProdIso`. -/
def unfold : ApproximableMap (iterSys V) (prod V (iterSys V)) := ofIso (iterProdIso V)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `head : D^∞ → D`, the top of the stack. -/
def head : ApproximableMap (iterSys V) V := (proj₀ V (iterSys V)).comp (unfold V)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem head_apply (z : (iterSys V).Element) :
    (head V).toElementMap z = component z 0 := by
  rw [head, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₀,
    iterProdIso_apply, fst_pair]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `tail : D^∞ → D^∞`, the stack with its top removed. -/
def tail : ApproximableMap (iterSys V) (iterSys V) := (proj₁ V (iterSys V)).comp (unfold V)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem tail_apply (z : (iterSys V).Element) :
    (tail V).toElementMap z = ofSeq (fun n => component z (n + 1)) := by
  rw [tail, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₁,
    iterProdIso_apply, snd_pair]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- The argument domain of `map`: a stack of functions paired with a point, `(D → D)^∞ × D`. -/
abbrev Arg (V : NeighborhoodSystem α) := prod (iterSys (funSpace V V)) V
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `diag : D → D^∞`, defined as the least fixed point of `s ↦ push(x, s)`. -/
def diag : ApproximableMap V (iterSys V) :=
  (fixMap (iterSys V)).comp (curry (push V))
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- The body of the `map` recursion as a two-argument map
`M(W, ⟨s, x⟩) = push((head s)(x), W(tail s, x))`, from which `map = fix(curry M)`. -/
def mapBody : ApproximableMap (prod (funSpace (Arg V) (iterSys V)) (Arg V)) (iterSys V) :=
  (push V).comp
    (paired
      ((evalMap V V).comp
        (paired
          ((head (funSpace V V)).comp ((proj₀ (iterSys (funSpace V V)) V).comp
            (proj₁ (funSpace (Arg V) (iterSys V)) (Arg V))))
          ((proj₁ (iterSys (funSpace V V)) V).comp
            (proj₁ (funSpace (Arg V) (iterSys V)) (Arg V)))))
      ((evalMap (Arg V) (iterSys V)).comp
        (paired (proj₀ (funSpace (Arg V) (iterSys V)) (Arg V))
          (paired
            ((tail (funSpace V V)).comp ((proj₀ (iterSys (funSpace V V)) V).comp
              (proj₁ (funSpace (Arg V) (iterSys V)) (Arg V))))
            ((proj₁ (iterSys (funSpace V V)) V).comp
              (proj₁ (funSpace (Arg V) (iterSys V)) (Arg V)))))))
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- The `map` recursion operator `R(W) = λ⟨s, x⟩. push((head s)(x), W(tail s, x))`. -/
def mapOp : ApproximableMap (funSpace (Arg V) (iterSys V)) (funSpace (Arg V) (iterSys V)) :=
  curry (mapBody V)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `map : (D → D)^∞ × D → D^∞`, the least fixed point of `mapOp`. -/
def mapMap : ApproximableMap (Arg V) (iterSys V) := toApproxMap (mapOp V).fixElement
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `(tail z)ₙ = zₙ₊₁`. -/
theorem component_tail (z : (iterSys V).Element) (n : ℕ) :
    component ((tail V).toElementMap z) n = component z (n + 1) := by
  rw [tail_apply, component_ofSeq]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L3031 EXERCISE 5.11 stack combinators -/
/-- **Exercise 5.11 (Scott 1981, PRG-19).** The recursion `diag(x) = push(x, diag(x))`. -/
theorem diag_rec (x : V.Element) :
    (diag V).toElementMap x =
      (push V).toElementMap (pair x ((diag V).toElementMap x)) := by
  rw [diag, toElementMap_comp]
  set φ := (curry (push V)).toElementMap x with hφ
  have hfix := fixMap_fixed (iterSys V) φ
  have hval := toElementMap_curry_apply (push V) x ((fixMap (iterSys V)).toElementMap φ)
  rw [← hφ] at hval
  rw [hval] at hfix
  exact hfix.symm
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

theorem fold_unfold (z : (iterSys V).Element) :
    (fold V).toElementMap ((unfold V).toElementMap z) = z := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

theorem mapBody_apply (W : (funSpace (Arg V) (iterSys V)).Element)
    (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapBody V).toElementMap (pair W (pair s x)) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((toApproxMap W).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  rw [mapBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 5.11 (Scott 1981, PRG-19).** The recursion defining `map`:
`map(s, x) = push((head s)(x), map(tail s, x))`. -/
theorem map_rec (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapMap V).toElementMap (pair s x) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  have hfix : (mapOp V).toElementMap (mapOp V).fixElement = (mapOp V).fixElement :=
    toElementMap_fixElement (mapOp V)
  have hval := toElementMap_curry_apply (mapBody V) (mapOp V).fixElement (pair s x)
  rw [← mapOp, hfix] at hval
  rw [mapMap, hval, mapBody_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Stack law.** `push(head z, tail z) = z` (a stack is its top pushed onto its tail). -/
theorem push_head_tail (z : (iterSys V).Element) :
    (push V).toElementMap (pair ((head V).toElementMap z) ((tail V).toElementMap z)) = z := by
  rw [head, tail, toElementMap_comp, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    pair_fst_snd, push, fold_unfold]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

theorem unfold_fold (p : (prod V (iterSys V)).Element) :
    (unfold V).toElementMap ((fold V).toElementMap p) = p := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Stack law.** `head(push(x, s)) = x`. -/
theorem head_push (x : V.Element) (s : (iterSys V).Element) :
    (head V).toElementMap ((push V).toElementMap (pair x s)) = x := by
  rw [head, toElementMap_comp, push, unfold_fold, toElementMap_proj₀, fst_pair]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Stack law.** `tail(push(x, s)) = s`. -/
theorem tail_push (x : V.Element) (s : (iterSys V).Element) :
    (tail V).toElementMap ((push V).toElementMap (pair x s)) = s := by
  rw [tail, toElementMap_comp, push, unfold_fold, toElementMap_proj₁, snd_pair]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 5.11 (Scott 1981, PRG-19).** Scott's emphasised property: *all* components of
`diag(x)` equal `x`, i.e. `diag(x) = ⟨x⟩ₙ`. -/
theorem component_diag (x : V.Element) (n : ℕ) :
    component ((diag V).toElementMap x) n = x := by
  induction n with
  | zero =>
    rw [← head_apply, diag_rec, head_push]
  | succ k ih =>
    have ht : (tail V).toElementMap ((diag V).toElementMap x) = (diag V).toElementMap x := by
      conv_lhs => rw [diag_rec]
      rw [tail_push]
    rw [← component_tail, ht, ih]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 5.11 (Scott 1981, PRG-19).** The `n`-th component of `map(s, x)` is `(component s n)(x)`,
i.e. `map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ`. -/
theorem component_map (x : V.Element) :
    ∀ (n : ℕ) (s : (iterSys (funSpace V V)).Element),
      component ((mapMap V).toElementMap (pair s x)) n =
        (toApproxMap (component s n)).toElementMap x := by
  intro n
  induction n with
  | zero =>
    intro s
    rw [← head_apply, map_rec, head_push, head_apply]
  | succ k ih =>
    intro s
    have ht : (tail V).toElementMap ((mapMap V).toElementMap (pair s x)) =
        (mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x) := by
      conv_lhs => rw [map_rec]
      rw [tail_push]
    rw [← component_tail, ht, ih, component_tail]
end

section
set_option linter.unusedVariables false

theorem example_511.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (s :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
        (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.iterSys α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
        (@DomainTheory.NeighbourhoodSystems.pair (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
          α
          (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
          V s x))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
        (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
                (@DomainTheory.NeighbourhoodSystems.Exercise511.head
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
            (@DomainTheory.NeighbourhoodSystems.pair
              (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
              (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
              V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.Exercise511.tail
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s)
              x))))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (s :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
        (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.iterSys α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
        (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
        (@DomainTheory.NeighbourhoodSystems.pair (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
          α
          (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
          V s x))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
        (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
        (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
                (@DomainTheory.NeighbourhoodSystems.Exercise511.head
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
            (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
            (@DomainTheory.NeighbourhoodSystems.pair
              (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
              (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
              V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                (@DomainTheory.NeighbourhoodSystems.Exercise511.tail
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                s)
              x)))))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V) x)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α (Prod Nat α)) (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V))
          (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.push α V)
          (@DomainTheory.NeighbourhoodSystems.pair α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) x
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x))))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Prod Nat α) V
              (@DomainTheory.NeighbourhoodSystems.iterSys α V) (@DomainTheory.NeighbourhoodSystems.Exercise511.diag α V)
              x)
            n)
          x)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (n : Nat)
        (s :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V))
            (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.component α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (Sum (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α) (Prod Nat α)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.Arg α V) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
              (@DomainTheory.NeighbourhoodSystems.Exercise511.mapMap α V)
              (@DomainTheory.NeighbourhoodSystems.pair
                (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)) α
                (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V))
                V s x))
            n)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
              (@DomainTheory.NeighbourhoodSystems.component (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) s n))
            x))
      @DomainTheory.NeighbourhoodSystems.Exercise511.component_diag
      @DomainTheory.NeighbourhoodSystems.Exercise511.component_map)
    @DomainTheory.NeighbourhoodSystems.Exercise511.diag_rec)
  @DomainTheory.NeighbourhoodSystems.Exercise511.map_rec
end

end DomainTheory.NeighbourhoodSystems.Exercise511
namespace DomainTheory.NeighbourhoodSystems.Exercise512
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The body of the loop as a two-argument map `M : (D → D) × D → D`,
`M(w, x) = cond(p(x), w(f(x)), x)`. It is assembled from `cond`, `eval`, the projections,
pairing and composition, hence approximable. -/
def bodyMap : ApproximableMap (prod (funSpace V V) V) V :=
  (cond V).comp
    (paired (p.comp (proj₁ (funSpace V V) V))
      (paired
        ((evalMap V V).comp
          (paired (proj₀ (funSpace V V) V) (f.comp (proj₁ (funSpace V V) V))))
        (proj₁ (funSpace V V) V)))
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The loop operator `Wop : (D → D) → (D → D)`, `Wop(w) = λx. cond(p(x), w(f(x)), x)`. -/
def Wop : ApproximableMap (funSpace V V) (funSpace V V) := curry (bodyMap V p f)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The `while`-loop element of the function space `D → D`: the least fixed point of `Wop`. -/
def whileFix : (funSpace V V).Element := (Wop V p f).fixElement
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The approximable function `while p do f : D → D` denoted by `whileFix`. -/
def whileMap : ApproximableMap V V := toApproxMap (whileFix V p f)
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- Value of the loop body: `M(w, x) = cond(p(x), w(f(x)), x)`. -/
theorem bodyMap_apply (w : (funSpace V V).Element) (x : V.Element) :
    (bodyMap V p f).toElementMap (pair w x) =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [bodyMap, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- `Wop(w)(x) = cond(p(x), w(f(x)), x)`. -/
theorem Wop_apply (w : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((Wop V p f).toElementMap w)).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [Wop, toElementMap_curry_apply, bodyMap_apply]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- **Leastness.** Any `w'` satisfying the `while`-recursion `w'(x) = cond(p(x), w'(f(x)), x)`
dominates the least solution `whileMap`. -/
theorem whileMap_least (w' : (funSpace V V).Element)
    (hw' : ∀ x : V.Element, (toApproxMap w').toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w').toElementMap (f.toElementMap x)) x))) :
    whileFix V p f ≤ w' := by
  apply fixElement_le_of_toElementMap_le
  apply le_of_eq
  apply (funSpaceEquiv V V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro x
  rw [Wop_apply]
  exact (hw' x).symm
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/- concordance: source L3071 EXERCISE 5.12 while combinator -/
/-- **Exercise 5.12 (Scott 1981, PRG-19).** The defining recursion of the `while`-loop:
`w(x) = cond(p(x), w(f(x)), x)`. -/
theorem whileMap_rec (x : V.Element) :
    (whileMap V p f).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((whileMap V p f).toElementMap (f.toElementMap x)) x)) := by
  have hfix : (Wop V p f).toElementMap (whileFix V p f) = whileFix V p f :=
    toElementMap_fixElement (Wop V p f)
  have := Wop_apply V p f (whileFix V p f) x
  rw [hfix] at this
  exact this
end

section
set_option linter.unusedVariables false

theorem example_512.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (p :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α DomainTheory.NeighbourhoodSystems.Example12.Token V
      DomainTheory.NeighbourhoodSystems.Exercise326.TD)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
      (@DomainTheory.NeighbourhoodSystems.Exercise512.whileMap α V p f) x)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
      (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
        DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
      V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
      (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
        DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
          DomainTheory.NeighbourhoodSystems.Example12.Token V DomainTheory.NeighbourhoodSystems.Exercise326.TD p x)
        (@DomainTheory.NeighbourhoodSystems.pair α α V V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.Exercise512.whileMap α V p f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x))
          x))) :=
  @DomainTheory.NeighbourhoodSystems.Exercise512.whileMap_rec
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- If the test diverges (`p(x) = ⊥`), the loop diverges: `w(x) = ⊥`. -/
theorem whileMap_bot {x : V.Element} (hx : p.toElementMap x = Example23.botElt) :
    (whileMap V p f).toElementMap x = V.bot := by
  rw [whileMap_rec, hx, Exercise326.cond_bot]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- If the test fails (`p(x) = false`), the loop exits: `w(x) = x`. -/
theorem whileMap_false {x : V.Element} (hx : p.toElementMap x = Example23.falseElt) :
    (whileMap V p f).toElementMap x = x := by
  rw [whileMap_rec, hx, Exercise326.cond_false]
end

section
variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- If the test holds (`p(x) = true`), the loop runs the body: `w(x) = w(f(x))`. -/
theorem whileMap_true {x : V.Element} (hx : p.toElementMap x = Example23.trueElt) :
    (whileMap V p f).toElementMap x = (whileMap V p f).toElementMap (f.toElementMap x) := by
  rw [whileMap_rec, hx, Exercise326.cond_true]
end

end DomainTheory.NeighbourhoodSystems.Exercise512
end

section
/- concordance: source L3149 EXERCISE 5.15 star of a word -/
-- Exercise515/kpow.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-- `zⁿ` as an iterated pointwise product (left-recursion `z^{n+1} = z·zⁿ`). -/
def kpow (z : Set S) : ℕ → Set S
  | 0 => 1
  | n + 1 => z * kpow z n

end DomainTheory.NeighbourhoodSystems.Exercise515
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise515
open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

section
variable {S : Type*} [Monoid S]

@[simp] theorem kpow_zero (z : Set S) : kpow z 0 = 1 := rfl
end

section
variable {S : Type*} [Monoid S]

@[simp] theorem kpow_succ (z : Set S) (n : ℕ) : kpow z (n + 1) = z * kpow z n := rfl
end

section
variable {S : Type*} [Monoid S]

/-- Scott's operator `w ↦ z·w ∪ v`, whose least fixed point is the least solution of `w = z·w ∪ v`. -/
def G (z v : Set S) (w : Set S) : Set S := z * w ∪ v
end

section
variable {S : Type*} [Monoid S]

/-- Scott's `z*`: the set of all finite products of elements of `z` (including the empty product
`1`). Defined as `{s ∣ ∃ n, s ∈ zⁿ}` to stay choice-free (avoiding `⋃` order lemmas). -/
def star (z : Set S) : Set S := {s | ∃ n, s ∈ kpow z n}
end

section
variable {S : Type*} [Monoid S]

/-- The "feedback" coefficient `A = a ∪ b·a*·b` of the eliminated system. -/
def parkA (a b : Set S) : Set S := a ∪ b * star a * b
end

section
variable {S : Type*} [Monoid S]

/-- The "feedback" constant `C = c ∪ b·a*·d`. -/
def parkC (a b c d : Set S) : Set S := c ∪ b * star a * d
end

section
variable {S : Type*} [Monoid S]

/-- Park's least solution for `x`: `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`. -/
def parkX (a b c d : Set S) : Set S := star (parkA a b) * parkC a b c d
end

section
variable {S : Type*} [Monoid S]

/-- The accompanying least solution for `y`: `y₀ = a*·(b·x₀ ∪ d)`. -/
def parkY (a b c d : Set S) : Set S := star a * (b * parkX a b c d ∪ d)
end

section
variable {S : Type*} [Monoid S]

/-- `{e}ⁿ = {eⁿ}` at the membership level (choice-free). -/
theorem mem_kpow_singleton (e s : S) (n : ℕ) : s ∈ kpow ({e} : Set S) n ↔ s = e ^ n := by
  induction n generalizing s with
  | zero => rw [kpow_zero, pow_zero]; exact Set.mem_one
  | succ m ih =>
      rw [kpow_succ, pow_succ', Set.mem_mul]
      constructor
      · rintro ⟨a, ha, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ha
        rw [(ih t).mp ht, ha]
      · rintro rfl
        exact ⟨e, Set.mem_singleton_iff.mpr rfl, e ^ m, (ih (e ^ m)).mpr rfl, rfl⟩
end

section
variable {S : Type*} [Monoid S]

theorem mem_star {z : Set S} {s : S} : s ∈ star z ↔ ∃ n, s ∈ kpow z n := Iff.rfl
end

section
variable {S : Type*} [Monoid S]

/-- `{e}* = e* = {Λ, e, e², …}`: a point lies in `star {e}` iff it is some power of `e`. -/
theorem mem_star_singleton (e s : S) : s ∈ star ({e} : Set S) ↔ ∃ n, s = e ^ n := by
  rw [mem_star]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_kpow_singleton e s n).mp hn⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (mem_kpow_singleton e (e ^ n) n).mpr rfl⟩
end

section
variable {S : Type*} [Monoid S]

/-- Associativity of the pointwise product (membership proof, choice-free). -/
theorem smul_assoc (a b c : Set S) : a * b * c = a * (b * c) := by
  ext s; simp only [Set.mem_mul]
  constructor
  · rintro ⟨u, ⟨p, hp, q, hq, rfl⟩, w, hw, rfl⟩
    exact ⟨p, hp, q * w, ⟨q, hq, w, hw, rfl⟩, by rw [mul_assoc]⟩
  · rintro ⟨p, hp, u, ⟨q, hq, w, hw, rfl⟩, rfl⟩
    exact ⟨p * q, ⟨p, hp, q, hq, rfl⟩, w, hw, by rw [mul_assoc]⟩
end

section
variable {S : Type*} [Monoid S]

/-- Left distributivity `a·(b ∪ c) = a·b ∪ a·c` (choice-free). -/
theorem smul_union (a b c : Set S) : a * (b ∪ c) = a * b ∪ a * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, hu, w, (hw | hw), rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, hu, w, Or.inl hw, rfl⟩
    · exact ⟨u, hu, w, Or.inr hw, rfl⟩
end

section
variable {S : Type*} [Monoid S]

/-- **Scott's unfolding** `z* = Λ ∪ z·z*`. -/
theorem star_eq (z : Set S) : star z = (1 : Set S) ∪ z * star z := by
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨n, hn⟩ := mem_star.mp hs
    cases n with
    | zero =>
        rw [kpow_zero] at hn
        rw [Set.mem_union]; exact Or.inl hn
    | succ m =>
        rw [kpow_succ, Set.mem_mul] at hn
        obtain ⟨a, ha, t, ht, rfl⟩ := hn
        rw [Set.mem_union]; right
        rw [Set.mem_mul]
        exact ⟨a, ha, t, mem_star.mpr ⟨m, ht⟩, rfl⟩
  · intro s hs
    rw [Set.mem_union] at hs
    rcases hs with h1 | h2
    · exact mem_star.mpr ⟨0, by rw [kpow_zero]; exact h1⟩
    · rw [Set.mem_mul] at h2
      obtain ⟨a, ha, t, ht, rfl⟩ := h2
      obtain ⟨m, hm⟩ := mem_star.mp ht
      exact mem_star.mpr ⟨m + 1, by rw [kpow_succ, Set.mem_mul]; exact ⟨a, ha, t, hm, rfl⟩⟩
end

section
variable {S : Type*} [Monoid S]

/-- For any prefixed point `w₀` of `w ↦ z·w ∪ v` (i.e. `z·w₀ ∪ v ⊆ w₀`), the candidate `z*·v` is
below `w₀`: the induction `zⁿ·v ⊆ w₀`. -/
theorem star_mul_subset_prefixed (z v x : Set S) (hx : z * x ∪ v ⊆ x) : star z * v ⊆ x := by
  have hvx : v ⊆ x := Set.subset_union_right.trans hx
  have hzx : z * x ⊆ x := Set.subset_union_left.trans hx
  have hpow : ∀ n, kpow z n * v ⊆ x := by
    intro n
    induction n with
    | zero => rw [kpow_zero, one_mul]; exact hvx
    | succ m ih =>
        rw [kpow_succ, smul_assoc]
        exact (Set.mul_subset_mul_left ih).trans hzx
  intro s hs
  rw [Set.mem_mul] at hs
  obtain ⟨a, ha, t, ht, rfl⟩ := hs
  obtain ⟨n, hn⟩ := mem_star.mp ha
  exact hpow n (by rw [Set.mem_mul]; exact ⟨a, hn, t, ht, rfl⟩)
end

section
variable {S : Type*} [Monoid S]

/-- Right distributivity `(a ∪ b)·c = a·c ∪ b·c` (choice-free). -/
theorem sunion_mul (a b c : Set S) : (a ∪ b) * c = a * c ∪ b * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, (hu | hu), w, hw, rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, Or.inl hu, w, hw, rfl⟩
    · exact ⟨u, Or.inr hu, w, hw, rfl⟩
end

section
variable {S : Type*} [Monoid S]

/-- `z*·v` is a fixed point of `w ↦ z·w ∪ v`: the star identity `z·(z*·v) ∪ v = z*·v`. -/
theorem star_mul_isFixed (z v : Set S) : z * (star z * v) ∪ v = star z * v := by
  conv_rhs => rw [star_eq z]
  rw [sunion_mul, one_mul, smul_assoc]
  exact Set.union_comm _ _
end

section
variable {S : Type*} [Monoid S]

/-- **Arden's lemma.** The least solution of `w = z·w ∪ v` in `P S` is `z*·v`. (Stated via
`lfpSet`, Exercise 4.14; the proof uses neither `Monotone` nor `⋃` order lemmas, so it is
choice-free.) -/
theorem arden (z v : Set S) : lfpSet (G z v) = star z * v := by
  apply Set.Subset.antisymm
  · exact lfpSet_least (G z v) (star_mul_isFixed z v)
  · intro s hs x hx
    exact star_mul_subset_prefixed z v x hx hs
end

section
variable {S : Type*} [Monoid S]

/-- `x₀` satisfies the first equation `x = a·x ∪ b·y ∪ c`. -/
theorem parkX_eq (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c := by
  have hfix : parkA a b * parkX a b c d ∪ parkC a b c d = parkX a b c d :=
    star_mul_isFixed (parkA a b) (parkC a b c d)
  conv_lhs => rw [← hfix]
  simp only [parkA, parkC, parkY, sunion_mul, smul_union, smul_assoc,
    Set.union_comm, Set.union_left_comm]
end

section
variable {S : Type*} [Monoid S]

/-- `y₀` satisfies the second equation `y = b·x ∪ a·y ∪ d`. -/
theorem parkY_eq (a b c d : Set S) :
    parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d := by
  have hfix : a * parkY a b c d ∪ (b * parkX a b c d ∪ d) = parkY a b c d :=
    star_mul_isFixed a (b * parkX a b c d ∪ d)
  conv_lhs => rw [← hfix]
  simp only [Set.union_assoc, Set.union_comm]
end

section
variable {S : Type*} [Monoid S]

/-- **Exercise 5.15(2), leastness.** Any solution `(x, y)` of the system dominates `(x₀, y₀)`. Hence
`(x₀, y₀)` is the *least* solution, and `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)` as claimed. The proof is
Gaussian elimination: solve the second equation for `y` by `arden`, substitute, apply `arden`
again. -/
theorem park_least (a b c d : Set S) {x y : Set S}
    (hx : x = a * x ∪ b * y ∪ c) (hy : y = b * x ∪ a * y ∪ d) :
    parkX a b c d ⊆ x ∧ parkY a b c d ⊆ y := by
  have hax : a * x ⊆ x := by
    calc a * x ⊆ a * x ∪ b * y ∪ c := Set.subset_union_left.trans Set.subset_union_left
      _ = x := hx.symm
  have hby : b * y ⊆ x := by
    calc b * y ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right.trans Set.subset_union_left
      _ = x := hx.symm
  have hcx : c ⊆ x := by
    calc c ⊆ a * x ∪ b * y ∪ c := Set.subset_union_right
      _ = x := hx.symm
  have hay : a * y ⊆ y := by
    calc a * y ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right.trans Set.subset_union_left
      _ = y := hy.symm
  have hbx : b * x ⊆ y := by
    calc b * x ⊆ b * x ∪ a * y ∪ d := Set.subset_union_left.trans Set.subset_union_left
      _ = y := hy.symm
  have hdy : d ⊆ y := by
    calc d ⊆ b * x ∪ a * y ∪ d := Set.subset_union_right
      _ = y := hy.symm
  -- The eliminated `y`: `a*·(b·x ∪ d) ⊆ y`.
  have hpre : a * y ∪ (b * x ∪ d) ⊆ y := Set.union_subset hay (Set.union_subset hbx hdy)
  have hyy : star a * (b * x ∪ d) ⊆ y := by
    rw [← arden a (b * x ∪ d)]
    exact lfpSet_subset (G a (b * x ∪ d)) hpre
  -- The decisive identity `(b·a*·b)·x ∪ b·a*·d = b·(a*·(b·x ∪ d))`.
  have key : b * star a * b * x ∪ b * star a * d = b * (star a * (b * x ∪ d)) := by
    simp only [smul_assoc, smul_union]
  -- `x` is a prefixed point of `w ↦ A·w ∪ C`, so `x₀ ⊆ x`.
  have hprefixX : parkA a b * x ∪ parkC a b c d ⊆ x := by
    have hmid : b * star a * b * x ∪ b * star a * d ⊆ x := by
      rw [key]; exact (Set.mul_subset_mul_left hyy).trans hby
    have hm1 : b * star a * b * x ⊆ x := Set.subset_union_left.trans hmid
    have hm2 : b * star a * d ⊆ x := Set.subset_union_right.trans hmid
    unfold parkA parkC
    rw [sunion_mul]
    exact Set.union_subset (Set.union_subset hax hm1) (Set.union_subset hcx hm2)
  have hPX : parkX a b c d ⊆ x := by
    have harden : parkX a b c d = lfpSet (G (parkA a b) (parkC a b c d)) :=
      (arden (parkA a b) (parkC a b c d)).symm
    rw [harden]
    exact lfpSet_subset (G (parkA a b) (parkC a b c d)) hprefixX
  have hPY : parkY a b c d ⊆ y := by
    show star a * (b * parkX a b c d ∪ d) ⊆ y
    have h1 : b * parkX a b c d ∪ d ⊆ b * x ∪ d :=
      Set.union_subset_union_left d (Set.mul_subset_mul_left hPX)
    exact (Set.mul_subset_mul_left h1).trans hyy
  exact ⟨hPX, hPY⟩
end

section
variable {S : Type*} [Monoid S]

/-- **Exercise 5.15(2), existence.** `(x₀, y₀)` solves David Park's system. -/
theorem park_solves (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
      parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d :=
  ⟨parkX_eq a b c d, parkY_eq a b c d⟩
end

section
variable {S : Type*} [Monoid S]

/-- **Exercise 5.15(1).** The least fixed point of `z = {e}·z ∪ {e'}` is `e*·{e'}` (`star {e}` is
`e*` by `mem_star_singleton`). -/
theorem part1 (e e' : S) :
    lfpSet (fun w => ({e} : Set S) * w ∪ {e'}) = star ({e} : Set S) * {e'} := by
  have hG : (fun w => ({e} : Set S) * w ∪ {e'}) = G ({e} : Set S) {e'} := rfl
  rw [hG]; exact arden {e} {e'}
end

section
set_option linter.unusedVariables false

theorem example_515.{u_1} : And
  (And
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S),
    And
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          c))
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          d))) :=
  @And.intro
  (And
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S),
    And
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          c))
      (@Eq (Set S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)
        (@Union.union (Set S) (@Set.instUnion S)
          (@Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              b (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d))
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              a (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d)))
          d)))
  (@And.intro
    (∀ {S : Type u_1} [inst : Monoid S] (e e' : S),
      @Eq (Set S)
        (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S fun (w : Set S) =>
          @Union.union (Set S) (@Set.instUnion S)
            (@HMul.hMul (Set S) (Set S) (Set S)
              (@instHMul (Set S)
                (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
              (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e) w)
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e'))
        (@HMul.hMul (Set S) (Set S) (Set S)
          (@instHMul (Set S) (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
          (@DomainTheory.NeighbourhoodSystems.Exercise515.star S inst
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e))
          (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) e')))
    (∀ {S : Type u_1} [inst : Monoid S] (a b c d : Set S) {x y : Set S},
      @Eq (Set S) x
          (@Union.union (Set S) (@Set.instUnion S)
            (@Union.union (Set S) (@Set.instUnion S)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                a x)
              (@HMul.hMul (Set S) (Set S) (Set S)
                (@instHMul (Set S)
                  (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                b y))
            c) →
        @Eq (Set S) y
            (@Union.union (Set S) (@Set.instUnion S)
              (@Union.union (Set S) (@Set.instUnion S)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  b x)
                (@HMul.hMul (Set S) (Set S) (Set S)
                  (@instHMul (Set S)
                    (@Set.mul S (@MulOne.toMul S (@MulOneClass.toMulOne S (@Monoid.toMulOneClass S inst)))))
                  a y))
              d) →
          And (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkX S inst a b c d) x)
            (@LE.le (Set S) (@Set.instLE S) (@DomainTheory.NeighbourhoodSystems.Exercise515.parkY S inst a b c d) y))
    @DomainTheory.NeighbourhoodSystems.Exercise515.part1 @DomainTheory.NeighbourhoodSystems.Exercise515.park_least)
  @DomainTheory.NeighbourhoodSystems.Exercise515.park_solves
end

section
variable {S : Type*} [Monoid S]

/-- The free semigroup `{0,1}*` of the exercise. Part (1) holds here as a special case. -/
theorem part1_freeMonoid (e e' : FreeMonoid Bool) :
    lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'})
      = star ({e} : Set (FreeMonoid Bool)) * {e'} :=
  part1 e e'
end

end DomainTheory.NeighbourhoodSystems.Exercise515
namespace DomainTheory.NeighbourhoodSystems.Exercise516
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Complement every bit of a finite string. -/
abbrev flip (σ : Str) : Str := σ.map not
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem flip_nil : flip [] = [] := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem flip_cons (b : Bool) (σ : Str) : flip (b :: σ) = (!b) :: flip σ := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem flip_flip (σ : Str) : flip (flip σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Double every bit of a finite string: `double (b :: σ) = b :: b :: double σ`. -/
def double : Str → Str
  | [] => []
  | b :: σ => b :: b :: double σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem double_nil : double [] = [] := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem double_cons (b : Bool) (σ : Str) : double (b :: σ) = b :: b :: double σ := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `double` distributes over append. -/
theorem double_append (σ τ : Str) : double (σ ++ τ) = double σ ++ double τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [double, ih]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `double` preserves the prefix order. -/
theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `flip` preserves the prefix order. -/
theorem flip_prefix {σ τ : Str} (h : σ <+: τ) : flip σ <+: flip τ := h.map _
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem not_strElem_le_strBot {σ τ : Str} : ¬ strElem σ ≤ strBot τ := by
  rw [strElem, strBot, C.principal_le_iff]
  exact not_cone_subset_singleton τ σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem strBot_le_strBot_iff {σ τ : Str} : strBot σ ≤ strBot τ ↔ σ <+: τ := by
  rw [strBot, strBot, C.principal_le_iff, cone_subset_cone]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem strBot_le_strElem_iff {σ τ : Str} : strBot σ ≤ strElem τ ↔ σ <+: τ := by
  rw [strBot, strElem, C.principal_le_iff]
  exact singleton_subset_cone
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem strElem_le_strElem_iff {σ τ : Str} : strElem σ ≤ strElem τ ↔ σ = τ := by
  rw [strElem, strElem, C.principal_le_iff, Set.singleton_subset_iff, Set.mem_singleton_iff,
    eq_comm]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The value of `tail` on a total element `σ`: `tail(Λ) = ⊥`, `tail(bσ') = σ'`. -/
def tailSing : Str → C.Element
  | [] => strBot []
  | _ :: σ' => strElem σ'
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem tail_hsing {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ tailSing τ := by
  cases τ with
  | nil => obtain rfl := List.prefix_nil.mp h; exact le_refl _
  | cons a τ' =>
    refine strBot_le_strElem_iff.mpr ?_
    cases σ with
    | nil => exact List.nil_prefix
    | cons b σ' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact h'
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- A prefix relation descends to tails. -/
theorem tail_prefix {σ τ : Str} (h : σ <+: τ) : σ.tail <+: τ.tail := by
  obtain ⟨ρ, rfl⟩ := h
  cases σ with
  | nil => simp
  | cons a σ' => exact List.prefix_append σ' ρ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem tail_hcone {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ strBot τ.tail :=
  strBot_le_strBot_iff.mpr (tail_prefix h)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/- concordance: source L3184 EXERCISE 5.16 negation of sequences -/
/-- **Exercise 5.16 / Example 4.4 — `tail : C → C`.** Built with the head-test combinator `liftC`:
on `σ⊥` it returns `(tail σ)⊥`, on `σ` the total `tail σ` (with `tail Λ = ⊥`). -/
def tailMap : ApproximableMap C C :=
  liftC C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem tailMap_strBot (σ : Str) :
    tailMap.toElementMap (strBot σ) = strBot σ.tail :=
  liftC_strBot C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem tailMap_strElem (σ : Str) :
    tailMap.toElementMap (strElem σ) = tailSing σ :=
  liftC_strElem C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem neg_hcone {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strBot (flip τ) :=
  strBot_le_strBot_iff.mpr (flip_prefix h)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem neg_hsing {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strElem (flip τ) :=
  strBot_le_strElem_iff.mpr (flip_prefix h)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 — `neg : C → C`.** The closed-form solution of Scott's recursion, built with
`liftC`: `neg(σ⊥) = (flip σ)⊥` and `neg(σ) = flip σ`. -/
def negMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem negMap_strBot (σ : Str) :
    negMap.toElementMap (strBot σ) = strBot (flip σ) :=
  liftC_strBot C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem negMap_strElem (σ : Str) :
    negMap.toElementMap (strElem σ) = strElem (flip σ) :=
  liftC_strElem C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem d_hcone {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strBot (double τ) :=
  strBot_le_strBot_iff.mpr (double_prefix h)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem d_hsing {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strElem (double τ) :=
  strBot_le_strElem_iff.mpr (double_prefix h)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 / Example 4.4 — `d : C → C`.** The doubling map, closed form via `liftC`:
`d(σ⊥) = (double σ)⊥`, `d(σ) = double σ`. -/
def dMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem dMap_strBot (σ : Str) :
    dMap.toElementMap (strBot σ) = strBot (double σ) :=
  liftC_strBot C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem dMap_strElem (σ : Str) :
    dMap.toElementMap (strElem σ) = strElem (double σ) :=
  liftC_strElem C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The neighbourhood of the tagged string `(b, σ)`: `{σ}` if total, `cone σ` if partial. -/
def shape : Bool → Str → Set Str
  | true, σ => {σ}
  | false, σ => cone σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem memC_shape : ∀ (b : Bool) (σ : Str), memC (shape b σ)
  | true, σ => memC_singleton σ
  | false, σ => memC_cone σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The element of the tagged string `(b, σ)`: total `σ` if `b`, partial `σ⊥` otherwise. -/
def shapeElem (b : Bool) (σ : Str) : C.Element := C.principal (memC_shape b σ)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem shapeElem_true (σ : Str) : shapeElem true σ = strElem σ := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem shapeElem_false (σ : Str) : shapeElem false σ = strBot σ := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The approximation order between tagged strings: `(b, σ) ⊑ (b', σ')`. A total string is maximal
(only `⊑` itself); a partial string `σ⊥` is `⊑` anything extending `σ`. -/
def SLe : Bool → Str → Bool → Str → Prop
  | true, σ, b', σ' => b' = true ∧ σ = σ'
  | false, σ, _, σ' => σ <+: σ'
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The interleave value function: `mergeVal σ b₀ τ b₁` returns the interleaving of the tagged
strings `(b₀, σ)` and `(b₁, τ)` as a tagged string. Boundary convention (the only monotone one):
`merge(Λ, y) = Λ`, `merge(⊥, y) = ⊥`, and `merge(εx, y) = ε⊥` once `y` runs out. -/
def mergeVal : Str → Bool → Str → Bool → Str × Bool
  | [], b₀, _, _ => ([], b₀)
  | a :: _, _, [], _ => ([a], false)
  | a :: σ, b₀, b :: τ, b₁ => (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem mergeVal_nil (b₀ : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal [] b₀ τ b₁ = ([], b₀) := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem mergeVal_cons_nil (a : Bool) (σ : Str) (b₀ b₁ : Bool) :
    mergeVal (a :: σ) b₀ [] b₁ = ([a], false) := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem mergeVal_cons_cons (a : Bool) (σ : Str) (b₀ b : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal (a :: σ) b₀ (b :: τ) b₁ =
      (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2) := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- Two equal head bits prepended preserve `SLe`. -/
theorem SLe_cons2 {p p' : Bool} {ρ ρ' : Str} (c d : Bool) (h : SLe p ρ p' ρ') :
    SLe p (c :: d :: ρ) p' (c :: d :: ρ') := by
  cases p with
  | true => obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | false =>
    exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, h⟩⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- Invert `SLe` on a cons in the first string: the second string starts with the same head. -/
theorem SLe_cons_inv {b₀ b₀' : Bool} {a : Bool} {σ₀ σ' : Str} (h : SLe b₀ (a :: σ₀) b₀' σ') :
    ∃ σ₀', σ' = a :: σ₀' ∧ SLe b₀ σ₀ b₀' σ₀' := by
  cases b₀ with
  | true =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨σ₀, rfl, rfl, rfl⟩
  | false =>
    cases σ' with
    | nil => exact absurd h (by simp [SLe])
    | cons a' σ₀' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact ⟨σ₀', rfl, h'⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The element produced by interleaving `(b₀, σ)` and `(b₁, τ)`. -/
def mergeElem (σ : Str) (b₀ : Bool) (τ : Str) (b₁ : Bool) : C.Element :=
  shapeElem (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **The monotonicity of interleaving.** If `(b₀, σ) ⊑ (b₀', σ')` and `(b₁, τ) ⊑ (b₁', τ')` then the
interleavings are `⊑`-ordered. The crux that makes `merge` approximable. -/
theorem mergeVal_SLe : ∀ (σ : Str) (b₀ : Bool) (σ' : Str) (b₀' : Bool)
    (τ : Str) (b₁ : Bool) (τ' : Str) (b₁' : Bool),
    SLe b₀ σ b₀' σ' → SLe b₁ τ b₁' τ' →
    SLe (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1
      (mergeVal σ' b₀' τ' b₁').2 (mergeVal σ' b₀' τ' b₁').1
  | [], b₀, σ', b₀', τ, b₁, τ', b₁', h0, _ => by
    cases b₀ with
    | true =>
      obtain ⟨rfl, rfl⟩ := h0
      simp only [mergeVal_nil]; exact ⟨rfl, rfl⟩
    | false =>
      simp only [mergeVal_nil]; exact List.nil_prefix
  | a :: σ₀, b₀, σ', b₀', [], b₁, τ', b₁', h0, _ => by
    obtain ⟨σ₀', rfl, _⟩ := SLe_cons_inv h0
    simp only [mergeVal_cons_nil]
    cases τ' with
    | nil => simp only [mergeVal_cons_nil]; exact List.prefix_rfl
    | cons c τ₀' => simp only [mergeVal_cons_cons]; exact ⟨c :: _, rfl⟩
  | a :: σ₀, b₀, σ', b₀', b :: τ₀, b₁, τ', b₁', h0, h1 => by
    obtain ⟨σ₀', rfl, h0'⟩ := SLe_cons_inv h0
    obtain ⟨τ₀', rfl, h1'⟩ := SLe_cons_inv h1
    simp only [mergeVal_cons_cons]
    exact SLe_cons2 a b (mergeVal_SLe σ₀ b₀ σ₀' b₀' τ₀ b₁ τ₀' b₁' h0' h1')
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- `SLe` characterizes the element order on `shapeElem`. -/
theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The element-order form of `mergeVal_SLe`. -/
theorem mergeElem_mono {σ σ' τ τ' : Str} {b₀ b₀' b₁ b₁' : Bool}
    (h0 : shapeElem b₀ σ ≤ shapeElem b₀' σ') (h1 : shapeElem b₁ τ ≤ shapeElem b₁' τ') :
    mergeElem σ b₀ τ b₁ ≤ mergeElem σ' b₀' τ' b₁' :=
  shapeElem_le_iff.mpr
    (mergeVal_SLe σ b₀ σ' b₀' τ b₁ τ' b₁' (shapeElem_le_iff.mp h0) (shapeElem_le_iff.mp h1))
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem shape_injective : ∀ {b b' : Bool} {σ σ' : Str}, shape b σ = shape b' σ' → b = b' ∧ σ = σ'
  | true, true, σ, σ', h => ⟨rfl, by rwa [shape, shape, Set.singleton_eq_singleton_iff] at h⟩
  | true, false, σ, σ', h => absurd h.symm (cone_ne_singleton σ' σ)
  | false, true, σ, σ', h => absurd h (cone_ne_singleton σ σ')
  | false, false, σ, σ', h => ⟨rfl, cone_injective h⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem shape_refine {b : Bool} {σ : Str} {P : Set Str} (hP : memC P) (hsub : P ⊆ shape b σ) :
    ∃ (b' : Bool) (σ' : Str), P = shape b' σ' ∧ shapeElem b σ ≤ shapeElem b' σ' := by
  rcases hP with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact ⟨false, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape false ρ)).mpr hsub⟩
  · exact ⟨true, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape true ρ)).mpr hsub⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The interleaving map `merge : C × C → C` with
`merge(εx, δy) = ε·δ·merge(x, y)`. Built directly as an approximable map: an input neighbourhood
`shape b₀ σ ∪ shape b₁ τ` relates to the neighbourhoods of `mergeElem σ b₀ τ b₁`. -/
def mergeMap : ApproximableMap (prod C C) C where
  rel W Z := ∃ (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str),
    W = prodNbhd (shape b₀ σ) (shape b₁ τ) ∧ (mergeElem σ b₀ τ b₁).mem Z
  rel_dom := by
    rintro W Z ⟨b₀, σ, b₁, τ, rfl, _⟩
    exact prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ)
  rel_cod := by
    rintro W Z ⟨b₀, σ, b₁, τ, _, hZ⟩
    exact (mergeElem σ b₀ τ b₁).sub hZ
  master_rel := by
    refine ⟨false, [], false, [], ?_, (mergeElem [] false [] false).master_mem⟩
    show (prod C C).master = prodNbhd (shape false []) (shape false [])
    simp only [prod_master, shape, C_master, cone_nil]
  inter_right := by
    rintro W Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ ⟨b₀', σ', b₁', τ', heq, hZ'⟩
    obtain ⟨hX, hY⟩ := prodNbhd_injective heq
    obtain ⟨rfl, rfl⟩ := shape_injective hX
    obtain ⟨rfl, rfl⟩ := shape_injective hY
    exact ⟨b₀, σ, b₁, τ, rfl, (mergeElem σ b₀ τ b₁).inter_mem hZ hZ'⟩
  mono := by
    rintro W W₂ Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ hW₂W hZZ' hW₂ hZ'
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hW₂
    obtain ⟨hPsub, hQsub⟩ := prodNbhd_subset_iff.mp hW₂W
    obtain ⟨b₀', σ', hPeq, hle0⟩ := shape_refine hP hPsub
    obtain ⟨b₁', τ', hQeq, hle1⟩ := shape_refine hQ hQsub
    subst hPeq; subst hQeq
    refine ⟨b₀', σ', b₁', τ', rfl, ?_⟩
    have hmono := mergeElem_mono hle0 hle1
    exact (mergeElem σ' b₀' τ' b₁').up_mem (hmono Z hZ) hZ' hZZ'
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

@[simp] theorem consMap_shapeElem (b c : Bool) (σ : Str) :
    (consMap b).toElementMap (shapeElem c σ) = shapeElem c (b :: σ) := by
  cases c with
  | false => rw [shapeElem_false, consMap_strBot]; rfl
  | true => rw [shapeElem_true, consMap_strElem]; rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- Two approximable maps out of `C` agree as soon as they agree on every finite element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below. -/
theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem memC_eq_shape {X : Set Str} (hX : memC X) : ∃ (b : Bool) (σ : Str), X = shape b σ := by
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨false, σ, rfl⟩
  · exact ⟨true, σ, rfl⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **The value of `merge` on a pair of finite elements.** `merge(⟨(b₀, σ), (b₁, τ)⟩) =
mergeElem σ b₀ τ b₁`. The analogue of `liftC_strBot`/`liftC_strElem` for the product. -/
theorem mergeMap_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    mergeMap.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ)) = mergeElem σ b₀ τ b₁ := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, c₀, ρ, c₁, π, rfl, hZ⟩
    rw [mem_pair_prodNbhd] at hWmem
    obtain ⟨hmσ, hmτ⟩ := hWmem
    have hle0 : shapeElem c₀ ρ ≤ shapeElem b₀ σ :=
      (C.principal_le_iff (memC_shape c₀ ρ) (memC_shape b₀ σ)).mpr hmσ.2
    have hle1 : shapeElem c₁ π ≤ shapeElem b₁ τ :=
      (C.principal_le_iff (memC_shape c₁ π) (memC_shape b₁ τ)).mpr hmτ.2
    exact mergeElem_mono hle0 hle1 Z hZ
  · intro hZ
    refine ⟨prodNbhd (shape b₀ σ) (shape b₁ τ), ?_, b₀, σ, b₁, τ, rfl, hZ⟩
    exact mem_pair_prodNbhd.mpr ⟨⟨memC_shape b₀ σ, subset_rfl⟩, ⟨memC_shape b₁ τ, subset_rfl⟩⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- The diagonal value: interleaving `(s, σ)` with itself doubles. -/
theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- On the diagonal `merge(⟨(s, σ), (s, σ)⟩)` doubles `σ`. -/
theorem mergeElem_diag (s : Bool) (σ : Str) : mergeElem σ s σ s = shapeElem s (double σ) := by
  simp [mergeElem, mergeVal_diag]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `merge(x, x) = d(x)` for all `x ∈ |C|` (the doubling map
of Example 4.4). -/
theorem mergeMap_diag (x : C.Element) :
    mergeMap.toElementMap (pair x x) = dMap.toElementMap x := by
  have key : mergeMap.comp (paired (idMap C) (idMap C)) = dMap := by
    apply map_ext_C
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strBot σ) (strBot σ) = pair (shapeElem false σ) (shapeElem false σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_false, dMap_strBot]
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strElem σ) (strElem σ) = pair (shapeElem true σ) (shapeElem true σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_true, dMap_strElem]
  have hx := congrArg (fun m : ApproximableMap C C => m.toElementMap x) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_idMap] at hx
  exact hx
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg ∘ neg = id` as approximable maps: it suffices to
check on the finite elements `σ⊥`, `σ`, where it is `flip ∘ flip = id`. -/
theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg(neg(x)) = x` for all `x ∈ |C|`. -/
theorem negMap_negMap (x : C.Element) : negMap.toElementMap (negMap.toElementMap x) = x := by
  have h := negMap_comp_negMap
  rw [← toElementMap_comp, h, toElementMap_idMap]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 — the recursion for `neg`, case `0`.** `neg(0·x) = 1·neg(x)` as a map identity. -/
theorem neg_cons_false : negMap.comp (consMap false) = (consMap true).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 — the recursion for `neg`, case `1`.** `neg(1·x) = 0·neg(x)` as a map identity. -/
theorem neg_cons_true : negMap.comp (consMap true) = (consMap false).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

theorem prod_principal_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    (prod C C).principal (prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ))
      = pair (shapeElem b₀ σ) (shapeElem b₁ τ) := by
  apply Element.ext
  intro P
  rw [mem_principal]
  constructor
  · rintro ⟨hP, hsub⟩
    obtain ⟨X', Y', hX', hY', rfl⟩ := hP
    obtain ⟨hsX, hsY⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
  · rintro ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
    exact ⟨prod_mem_prodNbhd hX' hY', prodNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- Two maps `C × C → C` agree as soon as they agree on every pair of finite elements. -/
theorem prodMap_ext {f g : ApproximableMap (prod C C) C}
    (h : ∀ b₀ σ b₁ τ, f.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))
      = g.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))) : f = g := by
  apply eq_of_toElementMap_principal
  intro W hW
  obtain ⟨b₀, σ, b₁, τ, rfl⟩ :
      ∃ b₀ σ b₁ τ, W = prodNbhd (shape b₀ σ) (shape b₁ τ) := by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    obtain ⟨b₀, σ, rfl⟩ := memC_eq_shape hX
    obtain ⟨b₁, τ, rfl⟩ := memC_eq_shape hY
    exact ⟨b₀, σ, b₁, τ, rfl⟩
  have heq : (prod C C).principal hW = pair (shapeElem b₀ σ) (shapeElem b₁ τ) :=
    prod_principal_pair b₀ σ b₁ τ
  rw [heq]; exact h b₀ σ b₁ τ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The defining recursion of `merge`:
`merge(εx, δy) = ε·δ·merge(x, y)` for all `x, y ∈ |C|` and bits `ε, δ`. -/
theorem mergeMap_cons (ε δ : Bool) (x y : C.Element) :
    mergeMap.toElementMap
        (pair ((consMap ε).toElementMap x) ((consMap δ).toElementMap y))
      = (consMap ε).toElementMap
          ((consMap δ).toElementMap (mergeMap.toElementMap (pair x y))) := by
  have key :
      mergeMap.comp (paired ((consMap ε).comp (proj₀ C C)) ((consMap δ).comp (proj₁ C C)))
        = ((consMap ε).comp (consMap δ)).comp mergeMap := by
    apply prodMap_ext
    intro b₀ σ b₁ τ
    simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
      fst_pair, snd_pair, consMap_shapeElem, mergeMap_pair, mergeElem, mergeVal_cons_cons]
  have hx := congrArg (fun m : ApproximableMap (prod C C) C => m.toElementMap (pair x y)) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair] at hx
  exact hx
end

section
set_option linter.unusedVariables false

theorem example_516 : And
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
  (@And.intro
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
    (@And.intro
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x)
      (@And.intro
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C))
        (@And.intro
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x))
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_cons
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_diag)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap_comp_negMap)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap_negMap)
    DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_false)
  DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_true
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- `tail(b(σ⊥)) = σ⊥`. -/
theorem tailMap_consMap_strBot (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strBot σ)) = strBot σ := by
  rw [consMap_strBot, tailMap_strBot]; rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
variable {β : Type*}

/-- `tail(b(σ)) = σ`. -/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b (¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem expand_nil : expand [] = [] := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

@[simp] theorem tmList_zero : tmList 0 = [] := rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t = 0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `σΣ* = Σ*` iff `σ = Λ`. -/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `expand` distributes over append (it is a monoid morphism `Σ* → Σ*`). -/
theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Each approximant is below the least fixed point. -/
theorem iterElem_le_fixElement {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
    (n : ℕ) : f.iterElem n ≤ f.fixElement := by
  rw [f.fixElement_eq_iSupDirected]
  intro Z hZ
  rw [mem_iSupDirected]
  exact ⟨n, hZ⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- A one-step unfolding of the iterated bottom element: `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate]
  exact Function.iterate_succ_apply' f.toElementMap n V.bot
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The base of the iterated bottom element: `f⁰(⊥) = ⊥`. -/
theorem iterElem_zero' {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) :
    f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Every iterate of `expand` from `[0]` starts with `0` (so `Φ` keeps acting as `expand`). -/
theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The second (total/partial-flag) component of an interleaving with a partial first input is always
`false`: a partial input keeps the output partial. -/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `(strBot τ)` has the cone of `σ` as a neighbourhood iff `σ` is a prefix of `τ`. -/
theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- `⊥ = []⊥` in `C` (the cone of `Λ` is the master). -/
theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 — the defining unfolding.** `t = 0·merge(neg t, tail t)`. -/
theorem tElt_unfold :
    (consMap false).toElementMap
        (mergeMap.toElementMap (pair (negMap.toElementMap tElt) (tailMap.toElementMap tElt)))
      = tElt := by
  have h := toElementMap_fixElement tmOp
  rw [tmOp, toElementMap_comp, toElementMap_comp, toElementMap_paired] at h
  exact h
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem tmList_length (n : ℕ) : (tmList n).length = n := by
  rw [tmList, List.length_map, List.length_range]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

theorem tmList_succ (n : ℕ) : tmList (n + 1) = tmList n ++ [tm n] := by
  simp only [tmList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Thue–Morse prefixes are nested in the prefix order. -/
theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The value of `Φ` on a partial element `σ⊥` is `(0 · weave σ)⊥`, the leading `0` prepended to the
interleaving of `(flip σ)⊥` and `(tail σ)⊥`. -/
theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The even recurrence `tm (2n) = tm n` (appending a `0`-digit does not change the parity). -/
theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The odd recurrence `tm (2n+1) = ¬ tm n` (appending a `1`-digit flips the parity). -/
theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly the even/odd parity
recurrence in disguise. -/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`. -/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The interleaving of `h :: flip ρ` with `ρ` (both starting after a common head `h`) is
`h :: expand ρ`. This is the heart of why `Φ` *is* the Thue–Morse morphism on the trajectory. -/
theorem weave_head : ∀ (h : Bool) (ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **The Thue–Morse trajectory.** On a partial element whose string starts with `0`, `Φ` acts as the
Thue–Morse morphism `expand`. -/
theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`. -/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']
end

section
set_option linter.unusedVariables false

theorem example_516_thue_morse : And
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C)
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  @And.intro
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C)
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
          DomainTheory.NeighbourhoodSystems.Example44.C
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
  DomainTheory.NeighbourhoodSystems.Exercise516.iterElem_succ_eq
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_unfold
end

section
open DomainTheory.NeighbourhoodSystems

/-- An **overlap** of period `p ≥ 1` at offset `i`: a factor of length `2p+1` with period `p`. -/
def Overlap (i p : ℕ) : Prop := 1 ≤ p ∧ ∀ k, k ≤ p → tm (i + k) = tm (i + p + k)
end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

/-- Positions differing by `|a|` inside `a ++ (a ++ a)` carry the same symbol, for indices `< 2|a|`
(the three copies of `a` are identical). -/
theorem append_three_period {α : Type*} (a : List α) (m : ℕ) (hm : m < 2 * a.length) :
    (a ++ (a ++ a))[m]? = (a ++ (a ++ a))[m + a.length]? := by
  rcases lt_or_ge m a.length with h | h
  · rw [List.getElem?_append_left h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h,
      List.getElem?_append_right (by omega : a.length ≤ m + a.length),
      show m + a.length - a.length = m by omega,
      List.getElem?_append_left (by omega : m - a.length < a.length),
      List.getElem?_append_right (by omega : a.length ≤ m)]
end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

/-- The `j`-th bit of the length-`n` Thue–Morse prefix is `tm j`. -/
theorem tmList_getElem? {n j : ℕ} (h : j < n) : (tmList n)[j]? = some (tm j) := by
  rw [tmList, List.getElem?_map, List.getElem?_range h]
  rfl
end

section
open DomainTheory.NeighbourhoodSystems

theorem tm_of_eq_two_mul {x y : ℕ} (h : x = 2 * y) : tm x = tm y := by
  rw [h, tm_two_mul]
end

section
open DomainTheory.NeighbourhoodSystems

theorem tm_of_eq_two_mul_add_one {x y : ℕ} (h : x = 2 * y + 1) : tm x = !tm y := by
  rw [h, tm_two_mul_add_one]
end

section
open DomainTheory.NeighbourhoodSystems

/-- An even-indexed symbol differs from its successor: `tm (2x) ≠ tm (2x+1)`. -/
theorem tm_two_mul_ne (x : ℕ) : tm (2 * x) ≠ tm (2 * x + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  cases tm x <;> simp
end

section
open DomainTheory.NeighbourhoodSystems

/-- `tm x = tm (x+1)` forces `x` to be **odd**: equal consecutive symbols only straddle a block
boundary `(2m+1, 2m+2)`, never a block `(2m, 2m+1)`. -/
theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd
end

section
open DomainTheory.NeighbourhoodSystems

/-- **No three consecutive equal symbols** (the period-`1` case): `¬ (tm j = tm (j+1) ∧
tm (j+1) = tm (j+2))`. If both held, `j` and `j+1` would both be odd. -/
theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega
end

section
open DomainTheory.NeighbourhoodSystems

/-- **Overlap-freeness of the Thue–Morse sequence** (Scott 1981, PRG-19; Thue 1912). No overlap
exists at any offset and period. -/
theorem no_overlap (p : ℕ) : ∀ i, ¬ Overlap i p := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro i hov
    obtain ⟨hp1, hrel⟩ := hov
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' p
    · -- Even period `p = 2q`: contract to a period-`q` overlap.
      subst hq
      have hq1 : 1 ≤ q := by omega
      obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
      · -- `i = 2a`: even positions give `tm (a+c) = tm (a+q+c)`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul (show i + 2 * c = 2 * (a + c) by omega),
          tm_of_eq_two_mul (show i + 2 * q + 2 * c = 2 * (a + q + c) by omega)] at this
        exact this
      · -- `i = 2a+1`: odd positions give `tm (a+c) = tm (a+q+c)` after stripping the `¬`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul_add_one (show i + 2 * c = 2 * (a + c) + 1 by omega),
          tm_of_eq_two_mul_add_one (show i + 2 * q + 2 * c = 2 * (a + q + c) + 1 by omega)] at this
        exact Bool.not_inj this
    · -- Odd period `p = 2q+1`.
      subst hq
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      · -- `p = 1`: three consecutive equal symbols.
        refine no_three_consec i ⟨?_, ?_⟩
        · have := hrel 0 (by omega); simpa using this
        · have := hrel 1 (by omega); simpa [show i + 1 + 1 = i + 2 by omega] using this
      · -- `p = 2q+1 ≥ 3`.
        obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
        · -- `i = 2a`: relations at `k = 0,1,2,3` give a run of three equal symbols at `a+q`.
          subst hi
          have r0 := hrel 0 (by omega)
          have r1 := hrel 1 (by omega)
          have r2 := hrel 2 (by omega)
          have r3 := hrel 3 (by omega)
          rw [tm_of_eq_two_mul (show 2 * a + 0 = 2 * a by omega),
            tm_of_eq_two_mul_add_one (show 2 * a + (2 * q + 1) + 0 = 2 * (a + q) + 1 by omega)] at r0
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 = 2 * a + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 1 = 2 * (a + q + 1) by omega)] at r1
          rw [tm_of_eq_two_mul (show 2 * a + 2 = 2 * (a + 1) by omega),
            tm_of_eq_two_mul_add_one
              (show 2 * a + (2 * q + 1) + 2 = 2 * (a + q + 1) + 1 by omega)] at r2
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 3 = 2 * (a + 1) + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 3 = 2 * (a + q + 2) by omega)] at r3
          refine no_three_consec (a + q) ⟨?_, ?_⟩
          · revert r0 r1; cases tm a <;> cases tm (a + q) <;> cases tm (a + q + 1) <;>
              simp_all
          · revert r1 r2 r3
            cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;> cases tm a <;>
              simp_all
        · -- `i = 2a+1`.
          subst hi
          rcases Nat.eq_or_lt_of_le hq1 with hq2 | hq2
          · -- `q = 1`, i.e. `p = 3`: a direct contradiction from the four relations.
            subst hq2
            have r0 := hrel 0 (by omega)
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 0 = 2 * a + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 0 = 2 * (a + 2) by omega)] at r0
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 1 = 2 * (a + 2) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 2 = 2 * (a + 3) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 3 = 2 * (a + 3) + 1 by omega)] at r3
            revert r0 r1 r2 r3
            cases tm a <;> cases tm (a + 1) <;> cases tm (a + 2) <;> cases tm (a + 3) <;> simp_all
          · -- `q ≥ 2`, i.e. `p ≥ 5`: relations at `k = 1,2,3,4` give a run of three at `a+q+1`.
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            have r4 := hrel 4 (by omega)
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 1 = 2 * (a + q + 1) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 2 = 2 * (a + q + 2) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 3 = 2 * (a + q + 2) + 1 by omega)] at r3
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 4 = 2 * (a + 2) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 4 = 2 * (a + q + 3) by omega)] at r4
            refine no_three_consec (a + q + 1) ⟨?_, ?_⟩
            · revert r1 r2; cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;>
                simp_all
            · revert r3 r4; cases tm (a + 2) <;> cases tm (a + q + 2) <;> cases tm (a + q + 3) <;>
                simp_all
end

section
open DomainTheory.NeighbourhoodSystems

/-- **The Thue–Morse sequence is cube-free.** A cube of period `p ≥ 1` (the factor `a·a·a` with
`|a| = p`) is in particular an overlap, so none exists. -/
theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Property (a), prefix form.** Every Thue–Morse parity prefix is a prefix of `t`:
`(tmList n)⊥ ⊑ t` for all `n`. -/
theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`. -/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h
end

section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Property (a) (Scott 1981, PRG-19; Lambek).** The finite-prefix characterization of `t`: a
string `σ` is a prefix of `t` **iff** it is the length-`σ.length` Thue–Morse parity prefix. Reading
off position `n`, the `n`-th digit of `t` is `tm n`, the parity of the binary digits of `n`. -/
theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ
    -- `σ` is a prefix of some Thue–Morse prefix `tmList N`.
    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero', mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩
    -- Both `σ` and `tmList σ.length` are the length-`σ.length` prefix of `tmList N`.
    have hlen : σ.length ≤ N := hpre.length_le.trans_eq (tmList_length _)
    have h1 : σ = (tmList N).take σ.length := List.prefix_iff_eq_take.mp hpre
    have h2 : tmList σ.length = (tmList N).take σ.length := by
      have := List.prefix_iff_eq_take.mp (tmList_prefix hlen)
      rwa [tmList_length] at this
    exact h1.trans h2.symm
  · intro hσ
    have h := tmList_le_tElt σ.length
    have hmem : (strBot (tmList σ.length)).mem (cone σ) :=
      strBot_mem_cone.mpr (hσ ▸ List.prefix_rfl)
    exact h _ hmem
end

section
open DomainTheory.NeighbourhoodSystems
open Example44 ExampleB NeighborhoodSystem

/-- **Exercise 5.16 (Scott 1981, PRG-19) — `t` is cube-free.** Scott's literal statement: `t` is not
of the form `u·a·a·a·v` for any finite prefix `u` and nonempty finite block `a`. (`v` is whatever
follows; we phrase "`u·a·a·a` is a prefix of `t`" as `(u·a·a·a)⊥ ⊑ t`.) -/
theorem tElt_cube_free (u a : Str) (ha : a ≠ []) :
    ¬ strBot (u ++ a ++ a ++ a) ≤ tElt := by
  intro hle
  -- `u·a·a·a` is a prefix of `t`, hence equals the Thue–Morse prefix of its length.
  have hmem : tElt.mem (cone (u ++ a ++ a ++ a)) :=
    hle _ (strBot_mem_cone.mpr List.prefix_rfl)
  have heq : u ++ a ++ a ++ a = tmList (u ++ a ++ a ++ a).length :=
    (tElt_mem_cone_iff _).mp hmem
  -- Read off a cube in `tm` at offset `|u|`, period `|a|`.
  set N := (u ++ a ++ a ++ a).length with hN
  have hlen : N = u.length + 3 * a.length := by simp only [hN, List.length_append]; omega
  have hp : 1 ≤ a.length := by
    cases a with
    | nil => exact (ha rfl).elim
    | cons _ _ => simp
  refine no_cube u.length a.length hp (fun k hk => ?_)
  -- Both `tm (|u|+k)` and `tm (|u|+|a|+k)` read the same bit of `u·a·a·a`.
  have hk3 : u.length + k < N := by omega
  have hk3' : u.length + a.length + k < N := by omega
  have e1 : (tmList N)[u.length + k]? = some (tm (u.length + k)) := tmList_getElem? hk3
  have e2 : (tmList N)[u.length + a.length + k]? = some (tm (u.length + a.length + k)) :=
    tmList_getElem? hk3'
  -- Rewrite the prefix as `u ++ (a ++ (a ++ a))` and strip `u`.
  have hassoc : u ++ a ++ a ++ a = u ++ (a ++ (a ++ a)) := by
    simp [List.append_assoc]
  rw [← heq, hassoc] at e1 e2
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + k),
    show u.length + k - u.length = k by omega] at e1
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + a.length + k),
    show u.length + a.length + k - u.length = k + a.length by omega] at e2
  -- Period: `(a++(a++a))[k]? = (a++(a++a))[k+|a|]?`.
  have hper := append_three_period a k (by omega)
  have : some (tm (u.length + k)) = some (tm (u.length + a.length + k)) := by
    rw [← e1, hper, e2]
  exact Option.some.inj this
end

section
set_option linter.unusedVariables false

theorem example_516_overlap : ∀ (u a : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
  @Ne DomainTheory.NeighbourhoodSystems.ExampleB.Str a (@List.nil Bool) →
    Not
      (@LE.le
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example44.C)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)))
        (DomainTheory.NeighbourhoodSystems.Example44.strBot
          (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
            (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
              (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool)) u a)
              a)
            a))
        DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_cube_free
end

end DomainTheory.NeighbourhoodSystems.Exercise516
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The **left-hand side** `λx. !y. τ(x, y)` of Proposition 5.4: `fix ∘ curry(τ)`. -/
def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The **operator** `λg. λx. τ(x, g(x))` of Proposition 5.4, as an approximable endomap of the
function space `(𝒟 → 𝒟)`: `recOp τ := curry(τ ∘ ⟨p₁, eval⟩)`. -/
def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The section `y ↦ τ(x, y)` of `τ : 𝒟 × 𝒟 → 𝒟` at a fixed `x`, as an approximable endomap of
`𝒟` (the curried `τ` applied to `x`). -/
def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `pfix τ (x) = !y. τ(x, y)`, the least fixed point of the section at `x`. -/
theorem pfix_apply (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    (pfix τ).toElementMap x = (section₂ τ x).fixElement := by
  rw [pfix, toElementMap_comp, fixMap_toElementMap, section₂]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `recOp τ (g) (x) = τ(x, g(x))`. -/
theorem recOp_apply (τ : ApproximableMap (prod V V) V) (φ : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((recOp τ).toElementMap φ)).toElementMap x
      = τ.toElementMap (pair x ((toApproxMap φ).toElementMap x)) := by
  rw [recOp, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem section₂_apply (τ : ApproximableMap (prod V V) V) (x y : V.Element) :
    (section₂ τ x).toElementMap y = τ.toElementMap (pair x y) := by
  rw [section₂, toElementMap_curry_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `pfix τ` is a fixed point of `recOp τ` (pointwise: `τ(x, pfix τ x) = pfix τ x`). -/
theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/- concordance: source L2799 PROPOSITION 5.4 fixed point under a parameter -/
/-- **Proposition 5.4 (Scott 1981, PRG-19).** `λx. !y. τ(x, y) = !g. λx. τ(x, g(x))`. -/
theorem pfix_eq_fixElement_recOp (τ : ApproximableMap (prod V V) V) :
    pfix τ = toApproxMap (recOp τ).fixElement := by
  set g₀ := (recOp τ).fixElement with hg₀
  set G := toApproxMap g₀ with hG
  -- `G(x) = τ(x, G(x))`: `g₀` is a fixed point of `recOp τ`.
  have hG_fixed : ∀ x, G.toElementMap x = τ.toElementMap (pair x (G.toElementMap x)) := by
    intro x
    have hfix : (recOp τ).toElementMap g₀ = g₀ := toElementMap_fixElement (recOp τ)
    have := recOp_apply τ g₀ x
    rw [hfix] at this
    rw [hG]; exact this
  apply le_antisymm
  · -- `pfix τ ⊑ G`: `pfix τ (x)` is the least fixed point of the section, `G(x)` is some fixed point.
    rw [le_iff_toElementMap_le]
    intro x
    rw [pfix_apply]
    apply fixElement_le_of_toElementMap_le
    rw [section₂_apply]
    exact le_of_eq (hG_fixed x).symm
  · -- `G ⊑ pfix τ`: `toFilter (pfix τ)` is a fixed point of `recOp τ`, so `g₀ ⊑ toFilter (pfix τ)`.
    have hpre : (recOp τ).toElementMap (toFilter (pfix τ)) ≤ toFilter (pfix τ) := by
      apply le_of_eq
      have hmap : toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ))) = pfix τ := by
        apply ext_of_toElementMap
        intro x
        rw [recOp_apply]
        have hround : toApproxMap (toFilter (pfix τ)) = pfix τ := by
          have he := (funSpaceEquiv V V).apply_symm_apply (pfix τ)
          rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
        rw [hround, pfix_isFixed]
      -- transport `hmap` through the iso `toApproxMap`/`toFilter`.
      have h1 : toFilter (toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ)))) =
          toFilter (pfix τ) := by rw [hmap]
      have hround2 : toFilter (toApproxMap ((recOp τ).toElementMap (toFilter (pfix τ)))) =
          (recOp τ).toElementMap (toFilter (pfix τ)) := by
        have he := (funSpaceEquiv V V).symm_apply_apply ((recOp τ).toElementMap (toFilter (pfix τ)))
        rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
      rw [hround2] at h1
      exact h1
    have hle : g₀ ≤ toFilter (pfix τ) := fixElement_le_of_toElementMap_le (recOp τ) hpre
    have := (funSpaceEquiv V V).monotone hle
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at this
    have hround : toApproxMap (toFilter (pfix τ)) = pfix τ := by
      have he := (funSpaceEquiv V V).apply_symm_apply (pfix τ)
      rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
    rw [hG, ← hround]
    exact this

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem theorem_54.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (τ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α α) α (@DomainTheory.NeighbourhoodSystems.prod α α V V) V),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.pfix α V τ)
    (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.recOp α V τ))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.pfix_eq_fixElement_recOp
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/- concordance: source L2836 TABLE 5.5 table of combinators -/
/-- **Table 5.5 (Scott 1981, PRG-19).** `P₀ = λx,y.x`, the first projection `𝒟₀ × 𝒟₁ → 𝒟₀`. -/
def P₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₀ :=
  proj₀ V₀ V₁
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem P₀_apply (x : V₀.Element) (y : V₁.Element) :
    (P₀ V₀ V₁).toElementMap (pair x y) = x := by
  rw [P₀, toElementMap_proj₀, fst_pair]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `P₁ = λx,y.y`, the second projection `𝒟₀ × 𝒟₁ → 𝒟₁`. -/
def P₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₁ :=
  proj₁ V₀ V₁
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem P₁_apply (x : V₀.Element) (y : V₁.Element) :
    (P₁ V₀ V₁).toElementMap (pair x y) = y := by
  rw [P₁, toElementMap_proj₁, snd_pair]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `diag = λx.⟨x,x⟩`, the diagonal `𝒟 → 𝒟 × 𝒟`. -/
def diagC (V : NeighborhoodSystem α) : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem diagC_apply (x : V.Element) : (diagC V).toElementMap x = pair x x := by
  rw [diagC, toElementMap_paired, toElementMap_idMap]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `pair = λx λy.⟨x,y⟩`, as the curried map
`𝒟₀ → (𝒟₁ → 𝒟₀ × 𝒟₁)`. -/
def pairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (funSpace V₁ (prod V₀ V₁)) := curry (idMap (prod V₀ V₁))
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** The base case `inv_{0,1}^2 = λx,y.⟨y,x⟩` of the
argument-swap scheme: `𝒟₀ × 𝒟₁ → 𝒟₁ × 𝒟₀`. -/
def swapC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) (prod V₁ V₀) := paired (proj₁ V₀ V₁) (proj₀ V₀ V₁)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem swapC_apply (x : V₀.Element) (y : V₁.Element) :
    (swapC V₀ V₁).toElementMap (pair x y) = pair y x := by
  rw [swapC, toElementMap_paired, toElementMap_proj₁, toElementMap_proj₀, snd_pair, fst_pair]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

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
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `comp = λg,f λx.g(f(x))` as an approximable map
`((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) → (𝒟₀ → 𝒟₂)`. -/
def compC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compMapTbl V₀ V₁ V₂)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `const = λk λx.k`, sending `k ∈ |𝒟₁|` to the constant map
`𝒟₀ → 𝒟₁`. Realized as `curry(p₀)`. -/
def constC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₁ (funSpace V₀ V₁) := curry (proj₀ V₁ V₀)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The order-isomorphism `|𝒟₀ × 𝒟₁ → 𝒟₂| ≃o |𝒟₀ → (𝒟₁ → 𝒟₂)|` between the *function-space
domains*, obtained from Theorem 3.10 (`funSpaceEquiv`) and Theorem 3.12 (`curryEquiv`). -/
def curryIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (funSpace (prod V₀ V₁) V₂).Element ≃o (funSpace V₀ (funSpace V₁ V₂)).Element :=
  (funSpaceEquiv (prod V₀ V₁) V₂).trans
    ((curryEquiv V₀ V₁ V₂).trans (funSpaceEquiv V₀ (funSpace V₁ V₂)).symm)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `curry = λg λx λy.g(x,y)` as an approximable map
`(𝒟₀ × 𝒟₁ → 𝒟₂) → (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
def curryC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace (prod V₀ V₁) V₂) (funSpace V₀ (funSpace V₁ V₂)) :=
  ofIso (curryIso V₀ V₁ V₂)
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `eval = λf,x.f(x)`, evaluation `(𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁`
(this is Theorem 3.11's `evalMap`). -/
def evalC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V₀ V₁) V₀) V₁ := evalMap V₀ V₁
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `fix = λf.!x.f(x)`, the least fixed-point operator
`(𝒟 → 𝒟) → 𝒟` (Theorem 4.2's `fixMap`). -/
def fixC (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V := fixMap V
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

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
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `funpair = λf λg λx.⟨f(x), g(x)⟩`, the curried operation
`(𝒟₂→𝒟₀) → ((𝒟₂→𝒟₁) → (𝒟₂ → 𝒟₀ × 𝒟₁))`. -/
def funpairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace V₂ V₀)
      (funSpace (funSpace V₂ V₁) (funSpace V₂ (prod V₀ V₁))) :=
  curry (curry (funpairMapTbl V₀ V₁ V₂))
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem compC_apply (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ))).toElementMap x
      = (toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x) := by
  rw [compC, toElementMap_curry_apply, compMapTbl]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `comp(g, f) = g ∘ f` (Scott's infix `g ∘ f`). -/
theorem compC_eq_comp (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ)) = (toApproxMap φ).comp (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, compC_apply]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem constC_apply (k : V₁.Element) (x : V₀.Element) :
    (toApproxMap ((constC V₀ V₁).toElementMap k)).toElementMap x = k := by
  rw [constC, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `const(k)` is the constant map `constMap` of Lemma 3.6. -/
theorem constC_eq_constMap (k : V₁.Element) :
    toApproxMap ((constC V₀ V₁).toElementMap k) = constMap V₀ k := by
  apply ext_of_toElementMap
  intro x
  rw [constC_apply, toElementMap_constMap]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `curry(g)` is the curried map of Theorem 3.12. -/
theorem curryC_toApproxMap (φ : (funSpace (prod V₀ V₁) V₂).Element) :
    toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ) = curry (toApproxMap φ) := by
  rw [curryC, toElementMap_ofIso]
  show toApproxMap (toFilter (curry (toApproxMap φ))) = curry (toApproxMap φ)
  have he := (funSpaceEquiv V₀ (funSpace V₁ V₂)).apply_symm_apply (curry (toApproxMap φ))
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem curryC_apply (φ : (funSpace (prod V₀ V₁) V₂).Element) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ)).toElementMap x)).toElementMap y
      = (toApproxMap φ).toElementMap (pair x y) := by
  rw [curryC_toApproxMap, toElementMap_curry_apply]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem evalC_apply (φ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (evalC V₀ V₁).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalC, evalMap_apply]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem fixC_apply (φ : (funSpace V V).Element) :
    (fixC V).toElementMap φ = (toApproxMap φ).fixElement := by
  rw [fixC, fixMap_toElementMap]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `fix(f) = f(fix(f))`. -/
theorem fixC_fixed (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixC V).toElementMap φ) = (fixC V).toElementMap φ := by
  rw [fixC]; exact fixMap_fixed V φ
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem funpairC_apply (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element)
    (x : V₂.Element) :
    (toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)).toElementMap x
      = pair ((toApproxMap φ).toElementMap x) ((toApproxMap ψ).toElementMap x) := by
  rw [funpairC, toElementMap_curry_apply, toElementMap_curry_apply, funpairMapTbl]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `funpair(f)(g)` is the paired map `⟨f, g⟩` of Definition 3.3. -/
theorem funpairC_eq_paired (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element) :
    toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)
      = paired (toApproxMap φ) (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [funpairC_apply, toElementMap_paired]
end

section
variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem pairC_apply (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((pairC V₀ V₁).toElementMap x)).toElementMap y = pair x y := by
  rw [pairC, toElementMap_curry_apply, toElementMap_idMap]
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The approximable map `y ↦ !x. τ(x, y)`: `fix ∘ curry(τ ∘ swap)`. -/
def secFixX (τ : ApproximableMap (prod V₀ V₁) V₀) : ApproximableMap V₁ V₀ :=
  (fixMap V₀).comp (curry (τ.comp (swapC V₁ V₀)))

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The outer operator `y ↦ σ(!x. τ(x, y), y)`. -/
def outerOp (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁) :
    ApproximableMap V₁ V₁ :=
  σ.comp (paired (secFixX τ) (idMap V₁))

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The section `x ↦ τ(x, y)` of `τ : 𝒟₀ × 𝒟₁ → 𝒟₀` at a fixed `y`, as an approximable endomap of
`𝒟₀` (the curried `τ ∘ swap` applied to `y`). -/
def sectionX (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) : ApproximableMap V₀ V₀ :=
  toApproxMap ((curry (τ.comp (swapC V₁ V₀))).toElementMap y)

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


theorem outerOp_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁)
    (y : V₁.Element) :
    (outerOp τ σ).toElementMap y = σ.toElementMap (pair ((secFixX τ).toElementMap y) y) := by
  rw [outerOp, toElementMap_comp, toElementMap_paired, toElementMap_idMap]

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


theorem secFixX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    (secFixX τ).toElementMap y = (sectionX τ y).fixElement := by
  rw [secFixX, toElementMap_comp, fixMap_toElementMap, sectionX]

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


theorem sectionX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) (x : V₀.Element) :
    (sectionX τ y).toElementMap x = τ.toElementMap (pair x y) := by
  rw [sectionX, toElementMap_curry_apply, toElementMap_comp, swapC_apply]

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


/-- `!x. τ(x, y)` is a fixed point of the section: `τ(!x.τ(x,y), y) = !x.τ(x,y)`. -/
theorem secFixX_isFixed (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    τ.toElementMap (pair ((secFixX τ).toElementMap y) y) = (secFixX τ).toElementMap y := by
  rw [secFixX_apply, ← sectionX_apply, toElementMap_fixElement]

end ApproximableMap
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap


/- concordance: source L2745 PROPOSITION 5.3 simultaneous fixed points -/
/-- **Proposition 5.3 (Scott 1981, PRG-19).** Bekić's theorem: the least fixed point of
`F = ⟨τ, σ⟩` is the pair `⟨!x.τ(x, !y.σ(x,y)-coordinate), !y.σ(!x.τ(x,y), y)⟩`. Here the second
coordinate is `ystar = (outerOp τ σ).fixElement` and the first is `xstar = secFixX τ (ystar)`. -/
theorem fixElement_paired_eq (τ : ApproximableMap (prod V₀ V₁) V₀)
    (σ : ApproximableMap (prod V₀ V₁) V₁) :
    (paired τ σ).fixElement =
      pair ((secFixX τ).toElementMap (outerOp τ σ).fixElement) (outerOp τ σ).fixElement := by
  set ystar := (outerOp τ σ).fixElement with hystar
  set xstar := (secFixX τ).toElementMap ystar with hxstar
  -- `σ(xstar, ystar) = ystar`: `ystar` is the fixed point of `outerOp`.
  have hσ : σ.toElementMap (pair xstar ystar) = ystar := by
    have := toElementMap_fixElement (outerOp τ σ)
    rw [← hystar] at this
    rw [outerOp_apply] at this
    rw [hxstar]; exact this
  -- `τ(xstar, ystar) = xstar`: `xstar = !x.τ(x, ystar)` is a fixed point of its section.
  have hτ : τ.toElementMap (pair xstar ystar) = xstar := by
    rw [hxstar]; exact secFixX_isFixed τ ystar
  apply le_antisymm
  · -- `F.fixElement ⊑ ⟨xstar, ystar⟩`: the pair is a fixed point of `F`.
    apply fixElement_le_of_toElementMap_le
    rw [toElementMap_paired]
    rw [hτ, hσ]
  · -- `⟨xstar, ystar⟩ ⊑ F.fixElement`.
    set fp := (paired τ σ).fixElement with hfp
    set a := fp.fst with ha
    set b := fp.snd with hb
    -- `τ(a, b) = a` and `σ(a, b) = b` (decompose the fixed point of `F`).
    have hfpeq : pair (τ.toElementMap fp) (σ.toElementMap fp) = fp := by
      have := toElementMap_fixElement (paired τ σ)
      rw [← hfp, toElementMap_paired] at this
      exact this
    have hfp_pair : fp = pair a b := (pair_fst_snd fp).symm
    have hτa : τ.toElementMap (pair a b) = a := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).fst = fp.fst := by rw [hfpeq]
      rw [fst_pair] at this
      rw [← hfp_pair]; rw [ha]; exact this
    have hσb : σ.toElementMap (pair a b) = b := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).snd = fp.snd := by rw [hfpeq]
      rw [snd_pair] at this
      rw [← hfp_pair]; rw [hb]; exact this
    -- `!x.τ(x, b) ⊑ a` since `τ(a, b) = a`.
    have hxfix_le : (secFixX τ).toElementMap b ≤ a := by
      rw [secFixX_apply]
      apply fixElement_le_of_toElementMap_le
      rw [sectionX_apply]
      exact le_of_eq hτa
    -- `outerOp(b) = σ(!x.τ(x,b), b) ⊑ σ(a, b) = b`.
    have houter_le : (outerOp τ σ).toElementMap b ≤ b := by
      rw [outerOp_apply]
      calc σ.toElementMap (pair ((secFixX τ).toElementMap b) b)
          ≤ σ.toElementMap (pair a b) :=
            σ.toElementMap_mono (pair_le_pair_iff.mpr ⟨hxfix_le, le_refl b⟩)
        _ = b := hσb
    -- so `ystar ⊑ b`, and `xstar = !x.τ(x, ystar) ⊑ !x.τ(x, b) ⊑ a`.
    have hystar_le : ystar ≤ b := by
      rw [hystar]
      exact fixElement_le_of_toElementMap_le (outerOp τ σ) houter_le
    have hxstar_le : xstar ≤ a := by
      rw [hxstar]
      calc (secFixX τ).toElementMap ystar
          ≤ (secFixX τ).toElementMap b := (secFixX τ).toElementMap_mono hystar_le
        _ ≤ a := hxfix_le
    rw [hfp_pair]
    exact pair_le_pair_iff.mpr ⟨hxstar_le, hystar_le⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem theorem_53.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (τ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₀)
  (σ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) β (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₁),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement (Sum α β)
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.paired α β (Sum α β) V₀ V₁ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        τ σ))
    (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α V₁ V₀
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.secFixX α β V₀ V₁ τ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.outerOp α β V₀ V₁ τ σ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.outerOp α β V₀ V₁ τ σ))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_paired_eq
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/- concordance: source L2599 THEOREM 5.1 terms denote approximable maps -/
/-- **Theorem 5.1, abstraction case (Scott 1981, PRG-19).** If `⟦σ⟧ : Γ × 𝒟ₙ → 𝒟'` is approximable,
then `λx.σ` is interpreted by `curry ⟦σ⟧ : Γ → (𝒟ₙ → 𝒟')` (approximable by Thm 3.12), with value
`(λx.σ)(v)(x) = σ(v, x)`. -/
theorem abs_apply (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem51
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, application case (Scott 1981, PRG-19).** If `⟦σ₀⟧ : Γ → (𝒟₀ → 𝒟₁)` and
`⟦σ₁⟧ : Γ → 𝒟₀` are approximable, then `σ₀(σ₁)` is interpreted by `eval ∘ ⟨⟦σ₀⟧, ⟦σ₁⟧⟩`
(approximable by Thm 3.11 and Thm 2.5), with value `(σ₀ w)(σ₁ w)`. -/
theorem app_apply (F : ApproximableMap V₂ (funSpace V₀ V₁)) (G : ApproximableMap V₂ V₀)
    (w : V₂.Element) :
    ((evalMap V₀ V₁).comp (paired F G)).toElementMap w
      = (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]

end Theorem51
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, constant case (Scott 1981, PRG-19).** A constant `k` is interpreted by the
constant map, which is approximable with value `k`. -/
theorem const_apply (k : V₁.Element) (x : V₀.Element) :
    (constMap V₀ k).toElementMap x = k := toElementMap_constMap k x

end Theorem51
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, tuple case (Scott 1981, PRG-19).** If `⟦σ₀⟧, ⟦σ₁⟧` are approximable, so is the
tuple `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired`, with value `⟨σ₀(w), σ₁(w)⟩`. -/
theorem tuple_apply (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) :=
  toElementMap_paired f g w

end Theorem51
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, variable case (Scott 1981, PRG-19).** A free variable is interpreted by a
projection of the context; the projections are approximable with `p₀⟨x,y⟩ = x`, `p₁⟨x,y⟩ = y`. -/
theorem var_fst (x : V₀.Element) (y : V₁.Element) :
    (proj₀ V₀ V₁).toElementMap (pair x y) = x := by rw [toElementMap_proj₀, fst_pair]

end Theorem51
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem51
section
set_option linter.unusedVariables false

theorem theorem_51.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                  (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
              x)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                  (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
              x)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x)
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                  (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
              x)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w)))
    (@And.intro
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                  (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
              x)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k)
      (@And.intro
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
          (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                  (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                  (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
              x)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w)))
        @DomainTheory.NeighbourhoodSystems.Theorem51.abs_apply @DomainTheory.NeighbourhoodSystems.Theorem51.app_apply)
      @DomainTheory.NeighbourhoodSystems.Theorem51.const_apply)
    @DomainTheory.NeighbourhoodSystems.Theorem51.tuple_apply)
  @DomainTheory.NeighbourhoodSystems.Theorem51.var_fst
end

end DomainTheory.NeighbourhoodSystems.Theorem51
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


theorem var_snd (x : V₀.Element) (y : V₁.Element) :
    (proj₁ V₀ V₁).toElementMap (pair x y) = y := by rw [toElementMap_proj₁, snd_pair]

end Theorem51
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/- concordance: source L2657 THEOREM 5.2 beta conversion -/
/-- **Theorem 5.2 (Scott 1981, PRG-19) — β as a map equation.** Substituting the constant `σ` for
the bound variable: `(λx.τ)(σ) = τ[σ/x]`, where the left side first abstracts (`curry g`) then
applies to the constant `σ`, and the right side substitutes `σ` directly. Both are approximable
maps `Γ → 𝒟'` and they are equal. -/
theorem beta (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element) :
    (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
      = g.comp (paired (idMap V₀) (constMap V₀ σ)) := by
  apply ext_of_toElementMap
  intro v
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply, toElementMap_curry_apply,
    toElementMap_constMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — abstraction case (`inv` step).**
`(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated at `y`: the double-curry application law. The bound `y` is
carried inert past the substitution of `σ` for `x`, exactly Scott's
`(λx.λy.τ)(σ)(y) = (λx.τ)(σ)`. -/
theorem beta_abs (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) (v : V₀.Element) (σ : V₁.Element)
    (y : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
      = g.toElementMap (pair (pair v σ) y) := by
  rw [toElementMap_curry_apply, toElementMap_curry_apply]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — tuple case.**
`(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`: abstraction distributes over a tuple. -/
theorem beta_tuple (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
    (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
      = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
          ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x) := by
  rw [toElementMap_curry_apply, toElementMap_paired, toElementMap_curry_apply,
    toElementMap_curry_apply]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2, base value law (Scott 1981, PRG-19).** `(λx.τ)(σ) = τ[σ/x]` evaluated: applying
the abstraction `curry g` (in free-variable context `v`) to `x` substitutes, giving `g(v, x)`. -/
theorem subst_value (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem52
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem52
section
set_option linter.unusedVariables false

theorem theorem_52.{u_1, u_2, u_3, u_5} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x)))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y)))
      @DomainTheory.NeighbourhoodSystems.Theorem52.beta @DomainTheory.NeighbourhoodSystems.Theorem52.beta_abs)
    @DomainTheory.NeighbourhoodSystems.Theorem52.beta_tuple)
  @DomainTheory.NeighbourhoodSystems.Theorem52.subst_value
end

end DomainTheory.NeighbourhoodSystems.Theorem52
namespace DomainTheory.NeighbourhoodSystems.Theorem56
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

section
/-- The unknown function `k` (`= proj₀`). -/
def kSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (funSpace (prod N N) N) :=
  proj₀ (funSpace (prod N N) N) (prod N N)
end

section
/-- The argument pair `⟨x, y⟩` (`= proj₁`). -/
def qSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (prod N N) :=
  proj₁ (funSpace (prod N N) N) (prod N N)
end

section
/-- The first argument `x`. -/
def argX : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₀ N N).comp qSel
end

section
/-- The second argument `y`. -/
def argY : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₁ N N).comp qSel
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The body `M(g, ⟨x, y⟩) = cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp (f.comp qSel))
      (paired argX
        ((evalMap (prod N N) N).comp
          (paired kSel (paired (succMap.comp argX) argY)))))

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The μ-operator `R(g) = λx,y. cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (muBody f)

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)

/-- `muRec f : N × N → N`, the binary search `ḡ`, least fixed point of `muOp`. -/
def muRec : ApproximableMap (prod N N) N := toApproxMap (muOp f).fixElement

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The minimization `μ : N → N`, `h̄(m) = ḡ(0̂, m)` (the strict `0`-seeded search). -/
def muMap : ApproximableMap N N := muRec f |>.comp (paired (constLiftN N (fun _ => zeroElt)) (idMap N))

end Mu
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

/-- The two-argument body `M(k, ⟨x, y⟩) = cond(zero(x), f(y), g(pred x, y, k(pred x, y)))`. -/
def primBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp argX)
      (paired (f.comp argY)
        (g.comp
          (paired (predMap.comp argX)
            (paired argY
              ((evalMap (prod N N) N).comp
                (paired kSel (paired (predMap.comp argX) argY))))))))

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

/-- The primitive-recursion operator `R(k) = λx,y. cond(zero x, f y, g(pred x, y, k(pred x, y)))`. -/
def primOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (primBody f g)

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

/-- `primRec f g : N × N → N`, the least fixed point of `primOp`. -/
def primRec : ApproximableMap (prod N N) N := toApproxMap (primOp f g).fixElement

end PrimRec
end

section
/-- Scott's **strict identity** `λx. cond(zero(x), x, x)`: the identity on totals, `⊥` on `⊥`. -/
def strictId : ApproximableMap N N :=
  (cond N).comp (paired zeroMap (paired (idMap N) (idMap N)))
end

section
/-- Scott's **strict first projection** `λx₀, x₁. cond(zero(x₁), x₀, x₀)` on `N × N`. -/
def strictProj₀ : ApproximableMap (prod N N) N :=
  (cond N).comp
    (paired (zeroMap.comp (proj₁ N N))
      (paired (proj₀ N N) (proj₀ N N)))
end

section
/-- The truth-domain bottom of `T` agrees with `Example23.botElt` (both are the least element).
Needed because `zeroMap_bot` lands in `T.bot` while `cond_bot` is phrased with `Example23.botElt`,
and `bot` is not reducible. -/
theorem T_bot_eq : (Example43.T).bot = Example23.botElt :=
  le_antisymm ((Example43.T).bot_le _) (Example23.botElt_le _)
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


theorem muBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (muBody f).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((toApproxMap k).toElementMap (pair (succMap.toElementMap x) y)))) := by
  rw [muBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- `μ(m̂) = ḡ(0̂, m̂)`. -/
theorem muMap_natElem (m : ℕ) :
    (muMap f).toElementMap (natElem m) = (muRec f).toElementMap (pair zeroElt (natElem m)) := by
  rw [muMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    constLiftN_natElem]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- The defining recursion of `muRec`. -/
theorem muRec_rec (x y : N.Element) :
    (muRec f).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((muRec f).toElementMap (pair (succMap.toElementMap x) y)))) := by
  have hfix : (muOp f).toElementMap (muOp f).fixElement = (muOp f).fixElement :=
    toElementMap_fixElement (muOp f)
  have hval := toElementMap_curry_apply (muBody f) (muOp f).fixElement (pair x y)
  rw [← muOp, hfix] at hval
  rw [muRec, hval, muBody_apply]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **μ is strict in the test.** If `f(n̂, m̂) = ⊥`, the search diverges. -/
theorem muRec_bot {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = N.bot) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = N.bot := by
  rw [muRec_rec, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **μ, found.** If `f(n̂, m̂) = 0̂`, the search stops and returns `n̂`. -/
theorem muRec_found {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem 0) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [muRec_rec, h, zeroMap_natElem_zero, Exercise326.cond_true]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **μ, step.** If `f(n̂, m̂)` is a positive total `(j+1)^`, the search advances to `n+1`. -/
theorem muRec_step {n m j : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem (j + 1)) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) =
      (muRec f).toElementMap (pair (natElem (n + 1)) (natElem m)) := by
  rw [muRec_rec, h, zeroMap_natElem_succ, Exercise326.cond_false, succMap_natElem]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- The search advances over a run of positive totals: if `f((n+i)^, m̂)` is a positive total for
all `i < k`, then `ḡ(n̂, m̂) = ḡ((n+k)^, m̂)`. -/
theorem muRec_climb (m : ℕ) :
    ∀ (k n : ℕ), (∀ i < k, ∃ j, f.toElementMap (pair (natElem (n + i)) (natElem m)) = natElem (j + 1)) →
      (muRec f).toElementMap (pair (natElem n) (natElem m)) =
        (muRec f).toElementMap (pair (natElem (n + k)) (natElem m)) := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.add_zero]
  | succ k ih =>
    intro n h
    obtain ⟨j, hj⟩ := h 0 (Nat.succ_pos k)
    rw [Nat.add_zero] at hj
    have key := ih (n + 1) (fun i hi => by
      obtain ⟨j', hj'⟩ := h (i + 1) (by omega)
      exact ⟨j', by rw [show n + 1 + i = n + (i + 1) by omega]; exact hj'⟩)
    rw [muRec_step f hj, key, show n + 1 + k = n + (k + 1) by omega]

end Mu
end

section
section Mu

variable (f : ApproximableMap (prod N N) N)


/-- **Capstone (μ-scheme correctness).** If `n₀` is the *least* zero of `f(·, m̂)` — that is,
`f(n̂₀, m̂) = 0̂` and `f(î, m̂)` is a positive total for every `i < n₀` — then `μ(m̂) = n̂₀`. -/
theorem muMap_eq_least {m n₀ : ℕ}
    (hzero : f.toElementMap (pair (natElem n₀) (natElem m)) = natElem 0)
    (hpos : ∀ i < n₀, ∃ j, f.toElementMap (pair (natElem i) (natElem m)) = natElem (j + 1)) :
    (muMap f).toElementMap (natElem m) = natElem n₀ := by
  rw [muMap_natElem]
  have hclimb := muRec_climb f m n₀ 0 (by simpa using hpos)
  rw [show (zeroElt : N.Element) = natElem 0 from rfl, hclimb, Nat.zero_add]
  exact muRec_found f hzero

end Mu
end

section
set_option linter.unusedVariables false

theorem theorem_56 : ∀
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum Nat Nat) Nat
      (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.N)
      DomainTheory.NeighbourhoodSystems.Example43.N)
  {m n₀ : Nat},
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum Nat Nat) Nat
        (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
          DomainTheory.NeighbourhoodSystems.Example43.N)
        DomainTheory.NeighbourhoodSystems.Example43.N f
        (@DomainTheory.NeighbourhoodSystems.pair Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
          DomainTheory.NeighbourhoodSystems.Example43.N (DomainTheory.NeighbourhoodSystems.Example43.natElem n₀)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem m)))
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    (∀ (i : Nat),
        @LT.lt Nat instLTNat i n₀ →
          ∃ (j : Nat),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum Nat Nat) Nat
                (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                DomainTheory.NeighbourhoodSystems.Example43.N f
                (@DomainTheory.NeighbourhoodSystems.pair Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
                  DomainTheory.NeighbourhoodSystems.Example43.N (DomainTheory.NeighbourhoodSystems.Example43.natElem i)
                  (DomainTheory.NeighbourhoodSystems.Example43.natElem m)))
              (DomainTheory.NeighbourhoodSystems.Example43.natElem
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) j
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
          DomainTheory.NeighbourhoodSystems.Example43.N)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
          DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
          (DomainTheory.NeighbourhoodSystems.Theorem56.muMap f) (DomainTheory.NeighbourhoodSystems.Example43.natElem m))
        (DomainTheory.NeighbourhoodSystems.Example43.natElem n₀) :=
  DomainTheory.NeighbourhoodSystems.Theorem56.muMap_eq_least
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


theorem primBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (primBody f g).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((toApproxMap k).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  rw [primBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- The defining recursion of `primRec`. -/
theorem primRec_rec (x y : N.Element) :
    (primRec f g).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((primRec f g).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  have hfix : (primOp f g).toElementMap (primOp f g).fixElement = (primOp f g).fixElement :=
    toElementMap_fixElement (primOp f g)
  have hval := toElementMap_curry_apply (primBody f g) (primOp f g).fixElement (pair x y)
  rw [← primOp, hfix] at hval
  rw [primRec, hval, primBody_apply]

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- **Primitive recursion is strict in the recursion argument.** `h̄(⊥, m̂) = ⊥`. -/
theorem primRec_bot (m : ℕ) :
    (primRec f g).toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [primRec_rec, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- **Primitive recursion, step case.** `h̄((n+1)^, m̂) = g(n̂, m̂, h̄(n̂, m̂))`. -/
theorem primRec_succ (n m : ℕ) :
    (primRec f g).toElementMap (pair (natElem (n + 1)) (natElem m)) =
      g.toElementMap
        (pair (natElem n)
          (pair (natElem m) ((primRec f g).toElementMap (pair (natElem n) (natElem m))))) := by
  rw [primRec_rec, zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ]

end PrimRec
end

section
section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


/-- **Primitive recursion, base case.** `h̄(0̂, m̂) = f(m̂)`. -/
theorem primRec_zero (m : ℕ) :
    (primRec f g).toElementMap (pair (natElem 0) (natElem m)) = f.toElementMap (natElem m) := by
  rw [primRec_rec, zeroMap_natElem_zero, Exercise326.cond_true]

end PrimRec
end

section
theorem strictId_bot : strictId.toElementMap N.bot = N.bot := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  rw [zeroMap_bot, T_bot_eq, Exercise326.cond_bot]
end

section
theorem strictId_natElem (n : ℕ) : strictId.toElementMap (natElem n) = natElem n := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  cases n with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]
end

section
theorem strictProj₀_apply (x y : N.Element) :
    strictProj₀.toElementMap (pair x y) =
      (cond N).toElementMap (pair (zeroMap.toElementMap y) (pair x x)) := by
  rw [strictProj₀, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair]
end

section
/-- Strict in the first argument: `proj₀(⊥, m̂) = ⊥` (the output *is* `x₀ = ⊥`). -/
theorem strictProj₀_bot_left (m : ℕ) :
    strictProj₀.toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]
end

section
/-- Strict in the second argument: `proj₀(n̂, ⊥) = ⊥`. -/
theorem strictProj₀_bot_right (n : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) N.bot) = N.bot := by
  rw [strictProj₀_apply, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]
end

section
/-- `proj₀(n̂, m̂) = n̂`. -/
theorem strictProj₀_natElem (n m : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]
end

end DomainTheory.NeighbourhoodSystems.Theorem56
namespace DomainTheory.NeighbourhoodSystems.Theorem56Full
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

section
/-- `none ↦ ⊥`, `some n ↦ n̂`. -/
def optElem : Option ℕ → N.Element
  | none => N.bot
  | some n => natElem n
end

section
/-- The universal argument domain `𝒩 = N^∞` (Exercise 3.16). All `k`-ary number functions are
realised as approximable maps `𝒩 → N` depending only on coordinates `0..k-1`. -/
abbrev 𝒩 : NeighborhoodSystem (ℕ × ℕ) := iterSys N
end

section
/-- A `𝒩`-element is *arg-like* if every coordinate is total or `⊥` (true of all `argElem`). -/
def ArgLike (z : 𝒩.Element) : Prop := ∀ j, component z j = N.bot ∨ ∃ k, component z j = natElem k
end

section
/-- The argument element of `𝒩` whose first `n` coordinates are `optElem (a i)` and the rest `⊥`. -/
def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)
end

section
/-- The argument element of `𝒩` carrying a `List.Vector ℕ n` in its first `n` coordinates. -/
def vecElem {n : ℕ} (v : List.Vector ℕ n) : 𝒩.Element :=
  argElem (fun i => some (v.get i))
end

section
/-- `φ : 𝒩 → N` realises the `n`-ary partial function `f` (a *very strict* λ-definition):
`φ` returns `f`'s value on total arguments, `⊥` where `f` is undefined, and `⊥` on *any* arg-like
input with a `⊥` among its first `n` coordinates. -/
structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot
end

section
@[simp] theorem component_argElem {n : ℕ} (a : Fin n → Option ℕ) (i : ℕ) :
    component (argElem a) i = if h : i < n then optElem (a ⟨i, h⟩) else N.bot := by
  rw [argElem, component_ofSeq]
end

section
@[simp] theorem component_vecElem {n : ℕ} (v : List.Vector ℕ n) (i : ℕ) :
    component (vecElem v) i = if h : i < n then natElem (v.get ⟨i, h⟩) else N.bot := by
  rw [vecElem, component_argElem]; split <;> rfl
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- `evalAt z` evaluates a function-space element at the fixed argument `z`. -/
def evalAt (z : 𝒩.Element) : ApproximableMap (funSpace 𝒩 N) N :=
  (evalMap 𝒩 N).comp (paired (idMap (funSpace 𝒩 N)) (constMap (funSpace 𝒩 N) z))

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- The search body `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail z)))`. -/
def findBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp (φf.comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩))
        ((evalMap 𝒩 N).comp
          (paired (proj₀ (funSpace 𝒩 N) 𝒩)
            ((push N).comp
              (paired (succMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))))

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- The search operator `S(k) = λz. …`, whose least fixed point is the running search. -/
def findOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (findBody φf)

end Rfind
end

section
/-- Test coordinate `j`: `cond(zero(zⱼ), φ z, φ z)`. -/
def guard1 (j : ℕ) (φ : ApproximableMap 𝒩 N) : ApproximableMap 𝒩 N :=
  (cond N).comp (paired (zeroMap.comp (projN N j)) (paired φ φ))
end

section
/-- Inject `N → 𝒩` as the stack whose only nonzero coordinate is the head. -/
def oneArg : ApproximableMap N 𝒩 := (push N).comp (paired (idMap N) (constMap N 𝒩.bot))
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)

/-- The primitive-recursion body. -/
def precBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired (φf.comp ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
        (φg.comp
          ((push N).comp
            (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
              ((push N).comp
                (paired
                  ((evalMap 𝒩 N).comp
                    (paired (proj₀ (funSpace 𝒩 N) 𝒩)
                      ((push N).comp
                        (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                          ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))
                  ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))))))))

end Prec
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)

/-- The primitive-recursion operator `R(k) = λz. …`. -/
def recOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (precBody φf φg)

end Prec
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)

/-- `recMap : 𝒩 → N`, the least fixed point of `recOp` (before strictifying). -/
def recMap : ApproximableMap 𝒩 N := toApproxMap (recOp φf φg).fixElement

end Prec
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- The `ℕ →. Bool` predicate `k ↦ f(k ::ᵥ v) = 0`, packaged so `Nat.rfind` is well-typed at
implicit transparency (Lean 4.33: `ℕ →. Bool` no longer unfolds to `ℕ → Part Bool` in `rw`). -/
def rfindZeroPred {n : ℕ} (f : List.Vector ℕ (n + 1) → ℕ) (v : List.Vector ℕ n) : ℕ →. Bool :=
  fun k => Part.some (decide (f (k ::ᵥ v) = 0))

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- `searchMap : 𝒩 → N`, the least fixed point of `findOp` (the counter lives in coordinate `0`). -/
def searchMap : ApproximableMap 𝒩 N := toApproxMap (findOp φf).fixElement

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- `findMap : 𝒩 → N` starts the search with counter `0`. -/
def findMap : ApproximableMap 𝒩 N :=
  (searchMap φf).comp ((push N).comp (paired (constMap 𝒩 (natElem 0)) (idMap 𝒩)))

end Rfind
end

section
/-- Test coordinates `0..n-1`. -/
def strictGuardN : ℕ → ApproximableMap 𝒩 N → ApproximableMap 𝒩 N
  | 0, φ => φ
  | n + 1, φ => guard1 n (strictGuardN n φ)
end

section
/-- `⟨g₀, …, g_{n-1}⟩ : 𝒩 → 𝒩` placing `gᵢ` at coordinate `i` (`< n`) and `⊥` beyond. -/
def tupleMap : (n : ℕ) → (Fin n → ApproximableMap 𝒩 N) → ApproximableMap 𝒩 𝒩
  | 0, _ => constMap 𝒩 𝒩.bot
  | n + 1, gs => (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ)))
end

section
/-- `T.bot = Example23.botElt` (both least); bridges `zeroMap_bot` (lands in `T.bot`) with `cond_bot`
(phrased with `Example23.botElt`). -/
theorem T_bot_eq : (Example43.T).bot = Example23.botElt :=
  le_antisymm ((Example43.T).bot_le _) (Example23.botElt_le _)
end

section
theorem argElem_argLike {n : ℕ} (a : Fin n → Option ℕ) : ArgLike (argElem a) := by
  intro j
  rw [component_argElem]
  split
  · cases h : a _ with
    | none => exact Or.inl rfl
    | some k => exact Or.inr ⟨k, rfl⟩
  · exact Or.inl rfl
end

section
/-- A coordinate that an `argElem` sets to `none` is `⊥`. -/
theorem component_argElem_none {n : ℕ} (a : Fin n → Option ℕ) (i : Fin n) (hi : a i = none) :
    component (argElem a) (i : ℕ) = N.bot := by
  rw [component_argElem, dite_eq_left i.isLt, Fin.eta, hi]; rfl
end

section
/-- Coordinates of the bottom stack are `⊥`. -/
theorem component_bot (i : ℕ) : component (𝒩.bot) i = N.bot := by
  have hbot : (𝒩.bot) = ofSeq (fun _ => N.bot) :=
    le_antisymm (𝒩.bot_le _)
      (le_of_component_le (fun i => by rw [component_ofSeq]; exact N.bot_le _))
  rw [hbot, component_ofSeq]
end

section
theorem component_push_succ (x : N.Element) (s : 𝒩.Element) (j : ℕ) :
    component ((push N).toElementMap (pair x s)) (j + 1) = component s j := by
  rw [← Exercise511.component_tail, Exercise511.tail_push]
end

section
theorem component_push_zero (x : N.Element) (s : 𝒩.Element) :
    component ((push N).toElementMap (pair x s)) 0 = x := by
  rw [← Exercise511.head_apply, Exercise511.head_push]
end

section
/-- Every coordinate `j < n` of `vecElem v` is the total `v.get j`. -/
theorem component_vecElem_lt {n : ℕ} (v : List.Vector ℕ n) {j : ℕ} (hj : j < n) :
    component (vecElem v) j = natElem (v.get ⟨j, hj⟩) := by
  rw [component_vecElem, dite_eq_left hj]
end

section
/-- Two `𝒩`-elements are equal iff all components agree. -/
theorem eq_of_component_eq {z z' : 𝒩.Element}
    (h : ∀ n, component z n = component z' n) : z = z' :=
  le_antisymm (le_of_component_le (fun n => (h n).le))
    (le_of_component_le (fun n => (h n).ge))
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


theorem evalAt_apply (z : 𝒩.Element) (φ : (funSpace 𝒩 N).Element) :
    (evalAt z).toElementMap φ = (toApproxMap φ).toElementMap z := by
  rw [evalAt, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap,
    evalMap_apply]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


theorem findBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (findBody φf).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap k).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  rw [findBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- The `0`-th approximant `S⁰(⊥)` is the bottom map. -/
theorem findOp_iterElem_zero : (findOp φf).iterElem 0 = (funSpace 𝒩 N).bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

end Rfind
end

section
theorem guard1_apply (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) :
    (guard1 j φ).toElementMap z =
      (cond N).toElementMap (pair (zeroMap.toElementMap (component z j))
        (pair (φ.toElementMap z) (φ.toElementMap z))) := by
  rw [guard1, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_projN]
end

section
theorem guard1_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : component z j = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rw [guard1_apply, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]
end

section
/-- If `φ z = ⊥` and `zⱼ` is total-or-`⊥`, the guard stays `⊥`. -/
theorem guard1_inner_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : component z j = N.bot ∨ ∃ k, component z j = natElem k)
    (h : φ.toElementMap z = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rcases hz with hb | ⟨k, hk⟩
  · exact guard1_bot j φ z hb
  · rw [guard1_apply, hk, h]
    cases k with
    | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
    | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]
end

section
theorem guard1_total (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) {k : ℕ}
    (h : component z j = natElem k) : (guard1 j φ).toElementMap z = φ.toElementMap z := by
  rw [guard1_apply, h]
  cases k with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- Recursion equation for the approximant values: `S^{m+1}(⊥)` unfolds one search step using
`Sᵐ(⊥)` as the continuation. -/
theorem iterVal_succ (m : ℕ) (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem (m + 1))).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap ((findOp φf).iterElem m)).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have h1 : (findOp φf).iterElem (m + 1) = (findOp φf).toElementMap ((findOp φf).iterElem m) := by
    rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]
  rw [h1]
  have hval := toElementMap_curry_apply (findBody φf) ((findOp φf).iterElem m) z
  rw [← findOp] at hval
  rw [hval, findBody_apply]

end Rfind
end

section
/-- A realiser of a total function evaluates to its value. -/
theorem lamDef_coe_val {n : ℕ} {φ : ApproximableMap 𝒩 N} {g : List.Vector ℕ n → ℕ}
    (h : LamDef φ (g : List.Vector ℕ n →. ℕ)) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = natElem (g v) :=
  h.defined v (g v) (by rw [PFun.coe_val]; exact Part.mem_some _)
end

section
/-- Transport a λ-definition along pointwise equality of the realised function. -/
theorem lamDef_congr {n : ℕ} {φ : ApproximableMap 𝒩 N} {f f' : List.Vector ℕ n →. ℕ}
    (h : ∀ v, f v = f' v) (hf : LamDef φ f) : LamDef φ f' where
  defined v c hc := hf.defined v c (by rw [h v]; exact hc)
  undef v hv := hf.undef v (by rw [h v]; exact hv)
  strict := hf.strict
end

section
/-- Membership in `mOfFn` (Part monad): a vector is produced iff each coordinate is a value. -/
theorem mem_mOfFn : ∀ {n : ℕ} (p : Fin n → Part ℕ) (w : List.Vector ℕ n),
    w ∈ List.Vector.mOfFn p ↔ ∀ i, w.get i ∈ p i
  | 0, p, w => by
      constructor
      · intro _ i; exact i.elim0
      · intro _
        show w ∈ (pure List.Vector.nil : Part _)
        rw [Part.pure_eq_some, Part.mem_some_iff]
        exact List.Vector.eq_nil w
  | n + 1, p, w => by
      have hmof : List.Vector.mOfFn p
          = (p 0).bind (fun a => (List.Vector.mOfFn fun i => p i.succ).bind
              (fun u => Part.some (a ::ᵥ u))) := by
        simp only [List.Vector.mOfFn, Part.bind_eq_bind, Part.pure_eq_some]
      rw [hmof, Part.mem_bind_iff]
      constructor
      · rintro ⟨a, ha, hrest⟩
        rw [Part.mem_bind_iff] at hrest
        obtain ⟨u, hu, hw⟩ := hrest
        rw [Part.mem_some_iff] at hw
        subst hw
        have hu' := (mem_mOfFn (fun i => p i.succ) u).mp hu
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ha
        · intro k; simpa using hu' k
      · intro hall
        refine ⟨w.head, ?_, ?_⟩
        · have := hall 0; rwa [List.Vector.get_zero] at this
        · rw [Part.mem_bind_iff]
          refine ⟨w.tail, (mem_mOfFn (fun i => p i.succ) w.tail).mpr (fun k => ?_), ?_⟩
          · have h := hall k.succ
            rwa [← List.Vector.get_tail_succ w k] at h
          · rw [Part.mem_some_iff]; exact (List.Vector.cons_head_tail w).symm
end

section
theorem oneArg_bot : (oneArg).toElementMap N.bot = 𝒩.bot := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  apply eq_of_component_eq
  intro i
  cases i with
  | zero => rw [component_push_zero, component_bot]
  | succ k => rw [component_push_succ, component_bot, component_bot]
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)


theorem precBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (precBody φf φg).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((toApproxMap k).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  rw [precBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end Prec
end

section
theorem push_natElem_vecElem {n : ℕ} (a : ℕ) (u : List.Vector ℕ n) :
    (push N).toElementMap (pair (natElem a) (vecElem u)) = vecElem (a ::ᵥ u) := by
  apply eq_of_component_eq
  intro j
  cases j with
  | zero =>
    rw [component_push_zero, component_vecElem, dite_eq_left (Nat.succ_pos n)]
    exact congrArg natElem (List.Vector.get_cons_zero a u).symm
  | succ k =>
    rw [component_push_succ, component_vecElem, component_vecElem]
    by_cases hk : k < n
    · rw [dite_eq_left hk, dite_eq_left (show k + 1 < n + 1 by omega)]
      exact congrArg natElem (List.Vector.get_cons_succ a u ⟨k, hk⟩).symm
    · rw [dite_eq_right hk, dite_eq_right (show ¬ k + 1 < n + 1 by omega)]
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


theorem findMap_vecElem {n : ℕ} (v : List.Vector ℕ n) :
    (findMap φf).toElementMap (vecElem v) = (searchMap φf).toElementMap (vecElem (0 ::ᵥ v)) := by
  rw [findMap, toElementMap_comp, toElementMap_comp, toElementMap_paired, toElementMap_constMap,
    toElementMap_idMap, push_natElem_vecElem]

end Rfind
end

section
theorem oneArg_natElem (a : ℕ) :
    (oneArg).toElementMap (natElem a) = vecElem (a ::ᵥ (List.Vector.nil : List.Vector ℕ 0)) := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  rw [show 𝒩.bot = vecElem (List.Vector.nil : List.Vector ℕ 0) from ?_, push_natElem_vecElem]
  exact eq_of_component_eq (fun i => by rw [component_bot, component_vecElem, dite_eq_right (by omega)])
end

section
/-- The value a realiser takes on a total argument is total-or-`⊥` (arg-like). -/
theorem realizer_value {n : ℕ} {φ : ApproximableMap 𝒩 N} {f : List.Vector ℕ n →. ℕ}
    (h : LamDef φ f) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = N.bot ∨ ∃ k, φ.toElementMap (vecElem v) = natElem k := by
  by_cases hd : (f v).Dom
  · exact Or.inr ⟨(f v).get hd, h.defined v _ (Part.get_mem hd)⟩
  · exact Or.inl (h.undef v hd)
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)


/-- The defining recursion equation. -/
theorem recMap_rec (z : 𝒩.Element) :
    (recMap φf φg).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((recMap φf φg).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  have hfix : (recOp φf φg).toElementMap (recOp φf φg).fixElement = (recOp φf φg).fixElement :=
    toElementMap_fixElement (recOp φf φg)
  have hval := toElementMap_curry_apply (precBody φf φg) (recOp φf φg).fixElement z
  rw [← recOp, hfix] at hval
  rw [recMap, hval, precBody_apply]

end Prec
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)


/-- **Primitive recursion computes.** `recMap(⟨d, u⟩) = (Nat.rec (f u) (g …) d)`. -/
theorem recMap_eval {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ)) (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ))
    (u : List.Vector ℕ n) (d : ℕ) :
    (recMap φf φg).toElementMap (vecElem (d ::ᵥ u))
      = natElem (Nat.rec (motive := fun _ => ℕ) (f₀ u)
          (fun y IH => g₀ (y ::ᵥ IH ::ᵥ u)) d) := by
  induction d with
  | zero =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_zero, Exercise326.cond_true]
    exact lamDef_coe_val hf u
  | succ d ih =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ, push_natElem_vecElem, ih,
      push_natElem_vecElem, push_natElem_vecElem]
    exact lamDef_coe_val hg _

end Prec
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- The defining recursion equation of the search. -/
theorem searchMap_rec (z : 𝒩.Element) :
    (searchMap φf).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((searchMap φf).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have hfix : (findOp φf).toElementMap (findOp φf).fixElement = (findOp φf).fixElement :=
    toElementMap_fixElement (findOp φf)
  have hval := toElementMap_curry_apply (findBody φf) (findOp φf).fixElement z
  rw [← findOp, hfix] at hval
  rw [searchMap, hval, findBody_apply]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- **Search step (found).** If `f(k ::ᵥ v) = 0`, the search returns the counter `k`. -/
theorem searchMap_step_found {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (h0 : f (k ::ᵥ v) = 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = natElem k := by
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), h0, zeroMap_natElem_zero,
    Exercise326.cond_true]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- **Search step (continue).** If `f(k ::ᵥ v) ≠ 0`, the search advances to counter `k + 1`. -/
theorem searchMap_step_next {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (hne : f (k ::ᵥ v) ≠ 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) =
      (searchMap φf).toElementMap (vecElem ((k + 1) ::ᵥ v)) := by
  obtain ⟨m, hm⟩ : ∃ m, f (k ::ᵥ v) = m + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hm, zeroMap_natElem_succ,
    Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- **Capstone (least zero ⟹ value).** If `m` is a zero of `f(· ::ᵥ v)` and nothing below it is, then
starting from any counter `j ≤ m` the search returns `m`. (Downward induction on `m - j`.) -/
theorem searchMap_climb {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (m : ℕ)
    (hm0 : f (m ::ᵥ v) = 0) (hmin : ∀ i, i < m → f (i ::ᵥ v) ≠ 0) :
    ∀ d j, j + d = m → (searchMap φf).toElementMap (vecElem (j ::ᵥ v)) = natElem m := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    rw [hjm]
    exact searchMap_step_found φf hf v m hm0
  | succ d ih =>
    intro j hj
    have hjm : j < m := by omega
    rw [searchMap_step_next φf hf v j (hmin j hjm)]
    exact ih (j + 1) (by omega)

end Rfind
end

section
/-- If some coordinate `i < n` is `⊥` (and `z` is arg-like), the guard forces `⊥`. -/
theorem strictGuardN_strict (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : ArgLike z) {i : ℕ} (hi : i < n) (hb : component z i = N.bot) :
    (strictGuardN n φ).toElementMap z = N.bot := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    rw [strictGuardN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact guard1_inner_bot m _ z (hz m) (ih hlt)
    · exact guard1_bot m _ z (heq ▸ hb)
end

section
/-- On arguments whose first `n` coordinates are all total, the guard is transparent. -/
theorem strictGuardN_total (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : ∀ j, j < n → ∃ k, component z j = natElem k) :
    (strictGuardN n φ).toElementMap z = φ.toElementMap z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := h m (Nat.lt_succ_self m)
    rw [strictGuardN, guard1_total m _ z hk]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- The least map of the function space evaluates to `⊥` everywhere. -/
theorem toApproxMap_bot (z : 𝒩.Element) :
    (toApproxMap ((funSpace 𝒩 N).bot)).toElementMap z = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  have h2 := (funSpaceEquiv 𝒩 N).monotone
    ((funSpace 𝒩 N).bot_le ((funSpaceEquiv 𝒩 N).symm (constMap 𝒩 N.bot)))
  rw [OrderIso.apply_symm_apply, funSpaceEquiv_apply] at h2
  have h3 := (le_iff_toElementMap_le.mp h2) z
  rwa [toElementMap_constMap] at h3

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- Value of the `0`-th approximant: `⊥`. -/
theorem iterVal_zero (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem 0)).toElementMap z = N.bot := by
  rw [findOp_iterElem_zero, toApproxMap_bot]

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- Along a *no-zero* trace, every finite approximant returns `⊥` (induction on the approximant
index, with the counter universally quantified since the search advances it). -/
theorem iterVal_bot {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) :
    ∀ m k, (toApproxMap ((findOp φf).iterElem m)).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  intro m
  induction m with
  | zero => intro k; exact iterVal_zero φf (vecElem (k ::ᵥ v))
  | succ m ih =>
    intro k
    have hne := hdiv k
    obtain ⟨j, hj⟩ : ∃ j, f (k ::ᵥ v) = j + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
    rw [← push_natElem_vecElem, iterVal_succ, Exercise511.head_push, Exercise511.tail_push,
      push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hj, zeroMap_natElem_succ,
      Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]
    exact ih (k + 1)

end Rfind
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- **Divergence.** If `f(· ::ᵥ v)` has no zero, the search is `⊥` from every counter. The fixed point
is the directed union of the approximants `Sᵐ(⊥)` (Theorem 4.2(iii)); pushing the evaluation at
`vecElem (k ::ᵥ v)` through this sup (continuity, `toElementMap_iSupDirected`) reduces the claim to
`iterVal_bot`. -/
theorem searchMap_diverge {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) (k : ℕ) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  rw [searchMap, ← evalAt_apply, fixElement_eq_iSupDirected, toElementMap_iSupDirected]
  apply NeighborhoodSystem.iSupDirected_le
  intro m
  rw [evalAt_apply]
  exact le_of_eq (iterVal_bot φf hf v hdiv m k)

end Rfind
end

section
theorem tupleMap_succ (n : ℕ) (gs : Fin (n + 1) → ApproximableMap 𝒩 N) :
    tupleMap (n + 1) gs = (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ))) := rfl
end

section
/-- Coordinate `i < n` of the tuple is exactly `gᵢ`. -/
theorem component_tupleMap : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ) (hi : i < n),
    component ((tupleMap n gs).toElementMap z) i = (gs ⟨i, hi⟩).toElementMap z
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, gs, z, 0, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_zero]
      exact congrArg (fun w => (gs w).toElementMap z) (Fin.ext (by simp))
  | n + 1, gs, z, i + 1, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ,
        component_tupleMap n (fun j => gs j.succ) z i (Nat.lt_of_succ_lt_succ hi)]
      rfl
end

section
theorem tupleMap_zero (gs : Fin 0 → ApproximableMap 𝒩 N) :
    tupleMap 0 gs = constMap 𝒩 𝒩.bot := rfl
end

section
/-- Coordinates `≥ n` of the tuple are `⊥`. -/
theorem component_tupleMap_ge : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ), n ≤ i → component ((tupleMap n gs).toElementMap z) i = N.bot
  | 0, gs, z, i, _ => by rw [tupleMap_zero, toElementMap_constMap, component_bot]
  | n + 1, gs, z, i, hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ]
      exact component_tupleMap_ge n (fun k => gs k.succ) z j (by omega)
end

section
/-- The tuple of realisers, applied to a total argument, is arg-like. -/
theorem tupleMap_argLike {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i)) (v : List.Vector ℕ m) :
    ArgLike ((tupleMap nn φg).toElementMap (vecElem v)) := by
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi]; exact realizer_value (hg ⟨i, hi⟩) v
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi)]; exact Or.inl rfl
end

section
/-- The tuple of realisers, applied to a total argument, equals `vecElem w` where `wᵢ = gᵢ(v)`. -/
theorem tupleMap_vecElem_eq {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i))
    (v : List.Vector ℕ m) (w : List.Vector ℕ nn) (hw : ∀ i, w.get i ∈ g i v) :
    (tupleMap nn φg).toElementMap (vecElem v) = vecElem w := by
  apply eq_of_component_eq
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi, component_vecElem_lt w hi]
    exact (hg ⟨i, hi⟩).defined v (w.get ⟨i, hi⟩) (hw ⟨i, hi⟩)
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi), component_vecElem,
      dite_eq_right hi]
end

section
/-- `vecElem v` has total coordinates throughout its arity. -/
theorem vecElem_totals {n : ℕ} (v : List.Vector ℕ n) :
    ∀ j, j < n → ∃ k, component (vecElem v) j = natElem k :=
  fun j hj => ⟨v.get ⟨j, hj⟩, component_vecElem_lt v hj⟩
end

section
/-- **Master constructor.** Wrapping an `inner` map (correct on total arguments) in `strictGuardN n`
yields a full, very strict λ-definition. The `strict` clause is then automatic. -/
theorem lamDef_of_inner {n : ℕ} (inner : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ)
    (hdef : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → inner.toElementMap (vecElem v) = natElem c)
    (hundef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → inner.toElementMap (vecElem v) = N.bot) :
    LamDef (strictGuardN n inner) f where
  defined v c hc := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hdef v c hc
  undef v hv := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hundef v hv
  strict z hz i hi hb := strictGuardN_strict n inner z hz hi hb
end

section
/-- **Composition** (Scott's multivariate composition). If `f` and each `gᵢ` are λ-defined, so is
`v ↦ (⟨g₀ v, …, g_{nn-1} v⟩) >>= f`. -/
theorem lamDef_comp {m nn : ℕ} (f : List.Vector ℕ nn →. ℕ) (g : Fin nn → List.Vector ℕ m →. ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf f)
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g i)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) := by
  refine lamDef_of_inner (φf.comp (tupleMap nn φg)) _ ?_ ?_
  · intro v c hc
    have hc' : c ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := hc
    rw [Part.mem_bind_iff] at hc'
    obtain ⟨w, hw, hcw⟩ := hc'
    rw [toElementMap_comp, tupleMap_vecElem_eq φg g hg v w ((mem_mOfFn _ w).mp hw)]
    exact hf.defined w c hcw
  · intro v hv
    rw [toElementMap_comp]
    by_cases hall : ∀ i, (g i v).Dom
    · set w : List.Vector ℕ nn := List.Vector.ofFn (fun i => (g i v).get (hall i)) with hw_def
      have hwget : ∀ i, w.get i ∈ g i v := by
        intro i; rw [hw_def, List.Vector.get_ofFn]; exact Part.get_mem (hall i)
      rw [tupleMap_vecElem_eq φg g hg v w hwget]
      refine hf.undef w (fun hfw => hv ?_)
      have hmem : (f w).get hfw ∈ (List.Vector.mOfFn fun i => g i v).bind (fun w => f w) := by
        rw [Part.mem_bind_iff]
        exact ⟨w, (mem_mOfFn _ w).mpr hwget, Part.get_mem hfw⟩
      exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
    · rw [not_forall] at hall
      obtain ⟨j, hj⟩ := hall
      refine hf.strict ((tupleMap nn φg).toElementMap (vecElem v))
        (tupleMap_argLike φg g hg v) j j.isLt ?_
      rw [component_tupleMap nn φg (vecElem v) j j.isLt, Fin.eta]
      exact (hg j).undef v hj
end

section
section Prec

variable (φf φg : ApproximableMap 𝒩 N)


/-- **Primitive recursion** (`Nat.Primrec'.prec` shape). -/
theorem lamDef_prec {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ))
    (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ)) :
    LamDef (strictGuardN (n + 1) (recMap φf φg))
      (((fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f₀ v.tail) fun y IH => g₀ (y ::ᵥ IH ::ᵥ v.tail)) :
        List.Vector ℕ (n + 1) → ℕ) : List.Vector ℕ (n + 1) →. ℕ) := by
  refine lamDef_of_inner (recMap φf φg) _ (fun v c hc => ?_)
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)
  rw [PFun.coe_val, Part.mem_some_iff] at hc
  subst hc
  obtain ⟨d, u, rfl⟩ := List.Vector.exists_eq_cons v
  rw [List.Vector.head_cons, List.Vector.tail_cons]
  exact recMap_eval φf φg f₀ g₀ hf hg u d

end Prec
end

section
/-- **Composition of total functions** (the `Nat.Primrec'.comp` shape). -/
theorem lamDef_primComp {m nn : ℕ} (f₀ : List.Vector ℕ nn → ℕ)
    (g₀ : Fin nn → List.Vector ℕ m → ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf (f₀ : List.Vector ℕ nn →. ℕ))
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g₀ i : List.Vector ℕ m →. ℕ)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      ((fun a => f₀ (List.Vector.ofFn fun i => g₀ i a) : List.Vector ℕ m → ℕ) :
        List.Vector ℕ m →. ℕ) := by
  refine lamDef_congr (fun v => ?_)
    (lamDef_comp (f₀ : _ →. ℕ) (fun i => (g₀ i : _ →. ℕ)) φf hf φg hg)
  simp only [PFun.coe_val, Vector.mOfFn_part_some]
  change (Part.some (List.Vector.ofFn fun i => g₀ i v)).bind (fun w => Part.some (f₀ w))
      = Part.some (f₀ (List.Vector.ofFn fun i => g₀ i v))
  exact Part.bind_some _ _
end

section
section Rfind

variable (φf : ApproximableMap 𝒩 N)


/-- **Minimisation** (`Nat.Partrec'.rfind` shape). Given a (very strict) realiser of a total
`f : Vector ℕ (n+1) → ℕ`, `strictGuardN n (findMap φf)` λ-defines
`v ↦ μk. f(k ::ᵥ v) = 0`. -/
theorem lamDef_rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) :
    LamDef (strictGuardN n (findMap φf))
      (fun v : List.Vector ℕ n => Nat.rfind (rfindZeroPred f v)) := by
  refine lamDef_of_inner (findMap φf) _ ?_ ?_
  · intro v c hc
    rw [findMap_vecElem]
    have hc' : c ∈ Nat.rfind (rfindZeroPred f v) := hc
    rw [Nat.mem_rfind] at hc'
    obtain ⟨hcs, hcm⟩ := hc'
    have h0 : f (c ::ᵥ v) = 0 := of_decide_eq_true (Part.mem_some_iff.mp hcs).symm
    have hmin : ∀ i, i < c → f (i ::ᵥ v) ≠ 0 :=
      fun i hi => of_decide_eq_false (Part.mem_some_iff.mp (hcm hi)).symm
    exact searchMap_climb φf hf v c h0 hmin c 0 (by omega)
  · intro v hv
    rw [findMap_vecElem]
    have hdiv : ∀ k, f (k ::ᵥ v) ≠ 0 := by
      intro k h0
      refine hv ?_
      have hdom : (Nat.rfind (rfindZeroPred f v)).Dom := by
        rw [Nat.rfind_dom]
        refine ⟨k, ?_, fun {m} _ => trivial⟩
        change true ∈ Part.some (decide (f (k ::ᵥ v) = 0))
        rw [Part.mem_some_iff]
        exact (decide_eq_true_iff.mpr h0).symm
      exact hdom
    exact searchMap_diverge φf hf v hdiv 0

end Rfind
end

section
/-- The total-function specialisation of `lamDef_of_inner`. -/
theorem lamDef_total {n : ℕ} (ψ : ApproximableMap 𝒩 N) (g : List.Vector ℕ n → ℕ)
    (hval : ∀ v, ψ.toElementMap (vecElem v) = natElem (g v)) :
    LamDef (strictGuardN n ψ) (g : List.Vector ℕ n →. ℕ) :=
  lamDef_of_inner ψ _
    (fun v c hc => by rw [PFun.coe_val, Part.mem_some_iff] at hc; rw [hval, ← hc])
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)
end

section
/-- `get i : Vector ℕ n → ℕ`, the `i`-th projection. -/
theorem lamDef_get {n : ℕ} (i : Fin n) :
    LamDef (strictGuardN n (projN N i))
      ((fun v => v.get i : List.Vector ℕ n → ℕ) : List.Vector ℕ n →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_projN, component_vecElem_lt v i.isLt, Fin.eta])
end

section
/-- `succ : Vector ℕ 1 → ℕ`, `v ↦ v.head + 1`. -/
theorem lamDef_succ : LamDef (strictGuardN 1 (succMap.comp (projN N 0)))
    ((fun v => Nat.succ v.head : List.Vector ℕ 1 → ℕ) : List.Vector ℕ 1 →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_comp, toElementMap_projN, component_vecElem_lt v (by norm_num),
      succMap_natElem]
    congr 1
    simp [List.Vector.get_zero])
end

section
/-- `zero : Vector ℕ 0 → ℕ`, the constant `0` (nullary). -/
theorem lamDef_zero : LamDef (strictGuardN 0 (constMap 𝒩 (natElem 0)))
    ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : List.Vector ℕ 0 →. ℕ) :=
  lamDef_total (constMap 𝒩 (natElem 0)) _ (fun v => by rw [toElementMap_constMap])
end

section
/-- **Every `Nat.Primrec'` function is λ-definable** by a (very strict) approximable map. -/
theorem primrec_lamDef {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Nat.Primrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ (f : List.Vector ℕ n →. ℕ) := by
  induction h with
  | zero => exact ⟨_, lamDef_zero⟩
  | succ => exact ⟨_, lamDef_succ⟩
  | get i => exact ⟨_, lamDef_get i⟩
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_primComp _ g φf hφf φg hφg⟩
  | prec _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      obtain ⟨φg, hφg⟩ := ihg
      exact ⟨_, lamDef_prec φf φg _ _ hφf hφg⟩
end

section
/- concordance: source L2877 THEOREM 5.6 partial recursive functions -/
/-- **Theorem 5.6 (Scott 1981, PRG-19) — every partial recursive function is λ-definable.** For each
`Nat.Partrec'` function `f : Vector ℕ n →. ℕ` there is an approximable map `φ : 𝒩 → N` that is a
*very strict* λ-definition of `f`: it returns `f`'s value on total arguments, `⊥` where `f` is
undefined, and `⊥` on any arg-like input with a `⊥` among its first `n` coordinates. -/
theorem partrec_lamDef {n : ℕ} {f : List.Vector ℕ n →. ℕ} (h : Nat.Partrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ f := by
  induction h with
  | prim hp => exact primrec_lamDef hp
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_comp _ g φf hφf φg hφg⟩
  | rfind _ ih =>
      obtain ⟨φf, hφf⟩ := ih
      exact ⟨_, lamDef_rfind φf hφf⟩
end

section
set_option linter.unusedVariables false

theorem theorem_56_full : ∀ {n : Nat} {f : PFun (List.Vector Nat n) Nat},
  @Nat.Partrec' n f →
    ∃ (φ :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat Nat) Nat
        DomainTheory.NeighbourhoodSystems.Theorem56Full.𝒩 DomainTheory.NeighbourhoodSystems.Example43.N),
      @DomainTheory.NeighbourhoodSystems.Theorem56Full.LamDef n φ f :=
  @DomainTheory.NeighbourhoodSystems.Theorem56Full.partrec_lamDef
end

section
/-- **Scott's 1-ary meta-theorem.** A partial recursive `h : ℕ →. ℕ` (presented as a unary
`Nat.Partrec'`) is denoted by a single approximable map `τ : N → N` that is correct on values,
divergent where `h` diverges, and strict. -/
theorem partrec_one {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot := by
  obtain ⟨φ, hφ⟩ := partrec_lamDef H
  refine ⟨φ.comp oneArg, ?_, ?_, ?_⟩
  · intro a m hm
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.defined (a ::ᵥ List.Vector.nil) m ?_
    rwa [List.Vector.head_cons]
  · intro a hdom
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.undef (a ::ᵥ List.Vector.nil) ?_
    rwa [List.Vector.head_cons]
  · rw [toElementMap_comp, oneArg_bot]
    refine hφ.strict 𝒩.bot (fun j => Or.inl (component_bot j)) 0 (by omega) (component_bot 0)
end

end DomainTheory.NeighbourhoodSystems.Theorem56Full
namespace DomainTheory.NeighbourhoodSystems.Exercise513
section
/-- One step of the diagonal walk: the cell holding `num c + 1`. Moving up-right within a diagonal,
or to the start of the next diagonal at the top edge. -/
def nextCell : ℕ × ℕ → ℕ × ℕ
  | (n + 1, m) => (n, m + 1)
  | (0, m) => (m + 1, 0)
end

section
/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2
end

section
/-- The pairing function `num n m = (n+m)(n+m+1)/2 + m` (Cantor's diagonal enumeration). -/
def num (n m : ℕ) : ℕ := tri (n + m) + m
end

section
/-- Its uncurried form, the actual `N × N → N` of the exercise. -/
def numP (p : ℕ × ℕ) : ℕ := num p.1 p.2
end

section
theorem num_succ_right (n m : ℕ) : num n (m + 1) = num (n + 1) m + 1 := by
  unfold num
  have h : n + (m + 1) = (n + 1) + m := by omega
  rw [h]; omega
end

section
theorem num_zero_zero : num 0 0 = 0 := rfl
end

section
/-- `k(k+1)` is even (choice-free, by induction). -/
theorem two_dvd_mul_succ (k : ℕ) : 2 ∣ k * (k + 1) := by
  induction k with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + (n + 1), ?_⟩
      have hexp : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [hexp, hc]; ring
end

section
/-- The defining doubling identity `2·T(k) = k(k+1)` — the division is exact because `k(k+1)` is
even. -/
theorem tri_mul_two (k : ℕ) : tri k * 2 = k * (k + 1) := by
  unfold tri
  exact Nat.div_mul_cancel (two_dvd_mul_succ k)
end

section
/-- The triangular recurrence `T(k+1) = T(k) + (k+1)`. -/
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have e1 : tri k * 2 = k * (k + 1) := tri_mul_two k
  have e2 : tri (k + 1) * 2 = (k + 1) * (k + 1 + 1) := tri_mul_two (k + 1)
  have key : tri (k + 1) * 2 = (tri k + (k + 1)) * 2 := by
    have hexp : (tri k + (k + 1)) * 2 = tri k * 2 + (k + 1) * 2 := by ring
    rw [hexp, e1, e2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key
end

section
/-- The value `num n m` sits in the half-open diagonal block `[T(n+m), T(n+m+1))`: the upper bound. -/
theorem num_lt_tri_succ (n m : ℕ) : num n m < tri (n + m + 1) := by
  rw [tri_succ]; unfold num; omega
end

section
theorem num_succ_left (n : ℕ) : num (n + 1) 0 = num 0 n + 1 := by
  unfold num
  have h0 : (n + 1) + 0 = n + 1 := by omega
  have h1 : 0 + n = n := by omega
  rw [h0, h1, tri_succ]; omega
end

section
theorem numP_nextCell (c : ℕ × ℕ) : numP (nextCell c) = numP c + 1 := by
  obtain ⟨n, m⟩ := c
  cases n with
  | zero => exact num_succ_left m
  | succ k => exact num_succ_right k m
end

section
theorem tri_le_succ (k : ℕ) : tri k ≤ tri (k + 1) := by
  rw [tri_succ]; omega
end

section
/-- `T` is monotone (proved by hand on `≤` to stay choice-free). -/
theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (tri_le_succ _)
end

section
/-- **The function is one-one.** The diagonal `s = n+m` is recovered as the unique `s` with
`T(s) ≤ num n m < T(s+1)`; then `m` is the offset and `n = s - m`. -/
theorem num_injective : Function.Injective numP := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ h
  have h' : num n₁ m₁ = num n₂ m₂ := h
  have hs : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · exfalso
      have h1 : num n₁ m₁ < tri (n₁ + m₁ + 1) := num_lt_tri_succ n₁ m₁
      have h2 : tri (n₁ + m₁ + 1) ≤ tri (n₂ + m₂) := tri_mono (by omega)
      have h3 : tri (n₂ + m₂) ≤ num n₂ m₂ := by unfold num; omega
      omega
    · exact heq
    · exfalso
      have h1 : num n₂ m₂ < tri (n₂ + m₂ + 1) := num_lt_tri_succ n₂ m₂
      have h2 : tri (n₂ + m₂ + 1) ≤ tri (n₁ + m₁) := tri_mono (by omega)
      have h3 : tri (n₁ + m₁) ≤ num n₁ m₁ := by unfold num; omega
      omega
  have hbase : tri (n₁ + m₁) + m₁ = tri (n₂ + m₂) + m₂ := h'
  rw [hs] at hbase
  have hm : m₁ = m₂ := by omega
  have hn : n₁ = n₂ := by omega
  subst hm; subst hn; rfl
end

section
/-- The inverse `unnum v = nextCellᵛ (0, 0)`. -/
def unnum : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | v + 1 => nextCell (unnum v)
end

section
theorem numP_unnum (v : ℕ) : numP (unnum v) = v := by
  induction v with
  | zero => exact num_zero_zero
  | succ k ih =>
      show numP (nextCell (unnum k)) = k + 1
      rw [numP_nextCell, ih]
end

section
theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])
end

section
variable {α β : Type*}

end

section
set_option linter.unusedVariables false

theorem example_513 : ∀ (c : Prod Nat Nat),
  @Eq (Prod Nat Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise513.unnum (DomainTheory.NeighbourhoodSystems.Exercise513.numP c)) c :=
  DomainTheory.NeighbourhoodSystems.Exercise513.unnum_numP
end

end DomainTheory.NeighbourhoodSystems.Exercise513
end

section
/- concordance: source L3119 EXERCISE 5.14 functions as graphs -/
-- Exercise514/tag.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- `tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m]`, built from the pairing function `num`. -/
def tag : List ℕ → ℕ → ℕ
  | [], m => num 0 m
  | (n :: ns), m => num (n + 1) (tag ns m)

end DomainTheory.NeighbourhoodSystems.Exercise514
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise514
open DomainTheory.NeighbourhoodSystems.Exercise513

section
@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl
end

section
@[simp] theorem tag_cons (n : ℕ) (ns : List ℕ) (m : ℕ) :
    tag (n :: ns) m = num (n + 1) (tag ns m) := rfl
end

section
/-- The finite set of entries of a list, as a subset of `ℕ`. -/
def entries (ns : List ℕ) : Set ℕ := {n | n ∈ ns}
end

section
@[simp] theorem mem_entries {n : ℕ} {ns : List ℕ} : n ∈ entries ns ↔ n ∈ ns := Iff.rfl
end

section
/-- `fun(u)(x)` — apply the "function coded by `u`" to argument `x`. -/
def Fun (u : Set ℕ) (x : Set ℕ) : Set ℕ :=
  {m | ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}
end

section
/-- `graph(f)` — the code of the function `f`. -/
def Graph (f : Set ℕ → Set ℕ) : Set ℕ :=
  {c | ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}
end

section
/-- A map `f : Pω → Pω` is *approximable* (continuous) when it is monotone and every output is
already produced by a finite subset of the input. The finite subsets of `x` are exactly the
`entries ns` with all entries in `x`.

Monotonicity is phrased as an explicit `⊆`-implication rather than `Monotone f`: on `Set ℕ` the
order `≤` resolves through the `CompleteLattice` instance whose construction uses `Classical.choice`,
so the `Monotone`-based statement would not be choice-free. The two are definitionally equal. -/
def IsApprox (f : Set ℕ → Set ℕ) : Prop :=
  (∀ ⦃x x' : Set ℕ⦄, x ⊆ x' → f x ⊆ f x') ∧
    ∀ x m, m ∈ f x → ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ m ∈ f (entries ns)
end

section
/-- Every `Fun u` is itself approximable, so `fun` really lands in the continuous maps. -/
theorem Fun_isApprox (u : Set ℕ) : IsApprox (Fun u) := by
  refine ⟨?_, ?_⟩
  · intro x x' hxx' m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, fun n hn => hxx' (hsub n hn), htag⟩
  · intro x m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, hsub, ns, fun n hn => hn, htag⟩
end

section
set_option linter.unusedVariables false

theorem example_514 : ∀ (u : Set Nat),
  DomainTheory.NeighbourhoodSystems.Exercise514.IsApprox (DomainTheory.NeighbourhoodSystems.Exercise514.Fun u) :=
  DomainTheory.NeighbourhoodSystems.Exercise514.Fun_isApprox
end

section
/-- **`Fun` is monotone in both arguments jointly.** Needed to check the `mono` axiom of the
neighbourhood-level approximable map built from `Fun` (Exercise 7.23). -/
theorem Fun_mono {u u' x x' : Set ℕ} (hu : u ⊆ u') (hx : x ⊆ x') : Fun u x ⊆ Fun u' x' := by
  rintro m ⟨ns, hns, htag⟩
  exact ⟨ns, fun n hn => hx (hns n hn), hu htag⟩
end

section
/-- `num (n+1) b` strictly exceeds its second argument: this is what makes the decode recursion
terminate. `num (n+1) b = T(n+1+b) + b ≥ (n+b+1) + b > b`. -/
theorem num_succ_left_gt (n b : ℕ) : b < num (n + 1) b := by
  unfold num
  have e : n + 1 + b = (n + b) + 1 := by omega
  rw [e, tri_succ]
  omega
end

section
/-- **The tag is one-one**, jointly in both arguments (induction on the list + `num_injective`). -/
theorem tag_injective : ∀ {ns₁ ns₂ : List ℕ} {m₁ m₂ : ℕ},
    tag ns₁ m₁ = tag ns₂ m₂ → ns₁ = ns₂ ∧ m₁ = m₂ := by
  intro ns₁
  induction ns₁ with
  | nil =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          have hp := num_injective (show numP (0, m₁) = numP (0, m₂) from h)
          injection hp with _ hm
          exact ⟨rfl, hm⟩
      | cons n₂ ns₂' =>
          exfalso
          have hp := num_injective (show numP (0, m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 _
          omega
  | cons n₁ ns₁' ih =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          exfalso
          have hp := num_injective (show numP (n₁ + 1, tag ns₁' m₁) = numP (0, m₂) from h)
          injection hp with h1 _
          omega
      | cons n₂ ns₂' =>
          have hp := num_injective
            (show numP (n₁ + 1, tag ns₁' m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 h2
          have hn : n₁ = n₂ := by omega
          obtain ⟨hns, hm⟩ := ih h2
          exact ⟨by rw [hn, hns], hm⟩
end

section
/-- **`fun ∘ graph = λf.f`** for continuous `f`: `Fun (Graph f) x = f x`. -/
theorem Fun_Graph {f : Set ℕ → Set ℕ} (hf : IsApprox f) (x : Set ℕ) :
    Fun (Graph f) x = f x := by
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    obtain ⟨ns', m', heq, hmem⟩ := htag
    obtain ⟨hns, hmm⟩ := tag_injective heq
    subst hns; subst hmm
    have hsubset : entries ns ⊆ x := fun n hn => hsub n hn
    exact hf.1 hsubset hmem
  · intro m hm
    obtain ⟨ns, hsub, hmem⟩ := hf.2 x m hm
    exact ⟨ns, hsub, ns, m, rfl, hmem⟩
end

section
/-- **The tag is onto**: every `c : ℕ` decodes as some `tag ns m`. Strong induction on `c`,
decreasing via `num_succ_left_gt`. -/
theorem tag_surjective (c : ℕ) : ∃ ns m, tag ns m = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      obtain ⟨a, b, hab⟩ : ∃ a b, num a b = c :=
        ⟨(unnum c).1, (unnum c).2, numP_unnum c⟩
      cases a with
      | zero => exact ⟨[], b, hab⟩
      | succ k =>
          have hlt : b < c := by rw [← hab]; exact num_succ_left_gt k b
          obtain ⟨ns, m, hns⟩ := ih b hlt
          exact ⟨k :: ns, m, by rw [tag_cons, hns]; exact hab⟩
end

section
/-- **`graph ∘ fun ⊇ λx.x`**: `u ⊆ Graph (Fun u)`. -/
theorem id_le_Graph_Fun (u : Set ℕ) : u ⊆ Graph (Fun u) := by
  intro c hc
  obtain ⟨ns, m, hceq⟩ := tag_surjective c
  refine ⟨ns, m, hceq.symm, ?_⟩
  exact ⟨ns, fun n hn => hn, by rw [hceq]; exact hc⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise514
namespace DomainTheory.NeighbourhoodSystems.Exercise513
section
/- concordance: source L3097 EXERCISE 5.13 pairing function on numbers -/
/-- **Exercise 5.13.** The pairing function packaged as a bijection `ℕ × ℕ ≃ ℕ` (choice-free, via the
explicit inverse `unnum`). -/
def numEquiv : ℕ × ℕ ≃ ℕ where
  toFun := numP
  invFun := unnum
  left_inv := unnum_numP
  right_inv := numP_unnum
end

section
@[simp] theorem numEquiv_apply (p : ℕ × ℕ) : numEquiv p = num p.1 p.2 := rfl
end

section
variable {α β : Type*}

/-- A bijection `α ≃ β` induces an order-isomorphism `P α ≅ P β` of power-set domains, by direct
image. -/
def setCongr (e : α ≃ β) : Set α ≃o Set β where
  toFun S := e '' S
  invFun T := e.symm '' T
  left_inv := e.symm_image_image
  right_inv := e.symm.symm_image_image
  map_rel_iff' := by
    intro a b
    constructor
    · intro h x hx
      obtain ⟨y, hy, hey⟩ := h ⟨x, hx, rfl⟩
      rwa [e.injective hey] at hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩
end

section
variable {α β : Type*}

/-- `P N ≅ P(N × N)` — induced by the pairing bijection `numEquiv`. -/
def PN_orderIso_PNN : Set ℕ ≃o Set (ℕ × ℕ) := setCongr numEquiv.symm
end

section
variable {α β : Type*}

/-- `P N ≅ P N × P N` — `N ≅ N ⊕ N` together with `P(A ⊕ B) ≅ P A × P B` (`Set.sumEquiv`). -/
def PN_orderIso_prod : Set ℕ ≃o Set ℕ × Set ℕ :=
  (setCongr Equiv.natSumNatEquivNat.symm).trans Set.sumEquiv
end

section
variable {α β : Type*}

/-- `P(N × N) ≅ P N × P N` — by composing the two isomorphisms above. -/
def PNN_orderIso_prod : Set (ℕ × ℕ) ≃o Set ℕ × Set ℕ :=
  PN_orderIso_PNN.symm.trans PN_orderIso_prod
end

end DomainTheory.NeighbourhoodSystems.Exercise513
end
