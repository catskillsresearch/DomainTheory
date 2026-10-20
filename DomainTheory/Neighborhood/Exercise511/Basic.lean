/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Theorem41

/-!
# Exercise 5.11 (Scott 1981, PRG-19, §5) — `D^∞` as stacks; stack combinators

Regarding `D^∞ = iterSys D` (Exercise 3.16) as (bottomless) *stacks* of elements of `D`, Scott asks
for combinators with the obvious meanings

```
head : D^∞ → D,      tail : D^∞ → D^∞,      push : D × D^∞ → D^∞,
```

then for `diag : D → D^∞` with `diag(x) = ⟨x⟩ₙ` (every component equal to `x`), defined by the
recursion `diag(x) = push(x, diag(x))`, and finally a combinator

```
map : (D → D)^∞ × D → D^∞,      map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ.
```

We build `head`, `tail`, `push` from the order-isomorphism `iterProdIso : D^∞ ≅ D × D^∞` of
Exercise 3.16 (so `unfold = ofIso iterProdIso`, `fold = ofIso iterProdIso.symm`), and obtain the
**stack laws**

* `head_push`  : `head(push(x, s)) = x`,
* `tail_push`  : `tail(push(x, s)) = s`,
* `push_head_tail` : `push(head z, tail z) = z`,

together with the component readings `head z = z₀` and `(tail z)ₙ = zₙ₊₁`.

`diag` and `map` are defined as least fixed points (Theorem 4.1/4.2); for `diag` we prove Scott's
emphasised property that **all** components equal `x` (`component_diag`), and for `map` that the
`n`-th component is `fₙ(x)` (`component_map`).

The only classical input is what is inherited from `iterProdIso` / `fixMap` and the project's
`Element.ext` machinery.
-/

namespace DomainTheory.Neighborhood.Exercise511

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### `unfold`/`fold` from the isomorphism `D^∞ ≅ D × D^∞`. -/

/-- `unfold : D^∞ → D × D^∞`, the forward direction of `iterProdIso`. -/
def unfold : ApproximableMap (iterSys V) (prod V (iterSys V)) := ofIso (iterProdIso V)

/-- `fold : D × D^∞ → D^∞`, the inverse direction of `iterProdIso`. -/
def fold : ApproximableMap (prod V (iterSys V)) (iterSys V) := ofIso (iterProdIso V).symm

/-- `iterProdIso` reads a stack as its head together with the tail sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

/-! ### The stack combinators. -/

/-- `head : D^∞ → D`, the top of the stack. -/
def head : ApproximableMap (iterSys V) V := (proj₀ V (iterSys V)).comp (unfold V)

/-- `tail : D^∞ → D^∞`, the stack with its top removed. -/
def tail : ApproximableMap (iterSys V) (iterSys V) := (proj₁ V (iterSys V)).comp (unfold V)

/-- `push : D × D^∞ → D^∞`, prepend an element to a stack. -/
def push : ApproximableMap (prod V (iterSys V)) (iterSys V) := fold V

@[simp] theorem head_apply (z : (iterSys V).Element) :
    (head V).toElementMap z = component z 0 := by
  rw [head, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₀,
    iterProdIso_apply, fst_pair]

@[simp] theorem tail_apply (z : (iterSys V).Element) :
    (tail V).toElementMap z = ofSeq (fun n => component z (n + 1)) := by
  rw [tail, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₁,
    iterProdIso_apply, snd_pair]

/-! ### `diag : D → D^∞`, the constant stack `⟨x⟩ₙ`, by recursion `diag(x) = push(x, diag(x))`. -/

/-- `diag : D → D^∞`, defined as the least fixed point of `s ↦ push(x, s)`. -/
def diag : ApproximableMap V (iterSys V) :=
  (fixMap (iterSys V)).comp (curry (push V))

/-! ### `map : (D → D)^∞ × D → D^∞`, `map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ`, by recursion. -/

/-- The argument domain of `map`: a stack of functions paired with a point, `(D → D)^∞ × D`. -/
abbrev Arg (V : NeighborhoodSystem α) := prod (iterSys (funSpace V V)) V

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

/-- The `map` recursion operator `R(W) = λ⟨s, x⟩. push((head s)(x), W(tail s, x))`. -/
def mapOp : ApproximableMap (funSpace (Arg V) (iterSys V)) (funSpace (Arg V) (iterSys V)) :=
  curry (mapBody V)

/-- `map : (D → D)^∞ × D → D^∞`, the least fixed point of `mapOp`. -/
def mapMap : ApproximableMap (Arg V) (iterSys V) := toApproxMap (mapOp V).fixElement
end DomainTheory.Neighborhood.Exercise511
