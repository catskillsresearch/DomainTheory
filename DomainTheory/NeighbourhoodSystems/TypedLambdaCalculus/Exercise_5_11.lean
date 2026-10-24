module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_3
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_11
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_25
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_20
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

@[expose] public section


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

end
end DomainTheory.NeighbourhoodSystems.Exercise511

section
namespace DomainTheory.NeighbourhoodSystems.Exercise511
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
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
end
