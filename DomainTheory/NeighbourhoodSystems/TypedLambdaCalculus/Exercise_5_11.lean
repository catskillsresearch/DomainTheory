module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_25
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_16
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_14

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α : Type*} (V : NeighborhoodSystem α)

def fold : ApproximableMap (prod V (iterSys V)) (iterSys V) := ofIso (iterProdIso V).symm

theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

def push : ApproximableMap (prod V (iterSys V)) (iterSys V) := fold V

def unfold : ApproximableMap (iterSys V) (prod V (iterSys V)) := ofIso (iterProdIso V)

def head : ApproximableMap (iterSys V) V := (proj₀ V (iterSys V)).comp (unfold V)

@[simp] theorem head_apply (z : (iterSys V).Element) :
    (head V).toElementMap z = component z 0 := by
  rw [head, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₀,
    iterProdIso_apply, fst_pair]

def tail : ApproximableMap (iterSys V) (iterSys V) := (proj₁ V (iterSys V)).comp (unfold V)

@[simp] theorem tail_apply (z : (iterSys V).Element) :
    (tail V).toElementMap z = ofSeq (fun n => component z (n + 1)) := by
  rw [tail, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₁,
    iterProdIso_apply, snd_pair]

abbrev Arg (V : NeighborhoodSystem α) := prod (iterSys (funSpace V V)) V

def diag : ApproximableMap V (iterSys V) :=
  (fixMap (iterSys V)).comp (curry (push V))

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

def mapOp : ApproximableMap (funSpace (Arg V) (iterSys V)) (funSpace (Arg V) (iterSys V)) :=
  curry (mapBody V)

def mapMap : ApproximableMap (Arg V) (iterSys V) := toApproxMap (mapOp V).fixElement

theorem component_tail (z : (iterSys V).Element) (n : ℕ) :
    component ((tail V).toElementMap z) n = component z (n + 1) := by
  rw [tail_apply, component_ofSeq]
end
end DomainTheory.NeighbourhoodSystems.Exercise511

section
namespace DomainTheory.NeighbourhoodSystems.Exercise511
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
section
variable {α : Type*} (V : NeighborhoodSystem α)

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

theorem fold_unfold (z : (iterSys V).Element) :
    (fold V).toElementMap ((unfold V).toElementMap z) = z := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply]

theorem mapBody_apply (W : (funSpace (Arg V) (iterSys V)).Element)
    (s : (iterSys (funSpace V V)).Element) (x : V.Element) :
    (mapBody V).toElementMap (pair W (pair s x)) =
      (push V).toElementMap
        (pair ((toApproxMap ((head (funSpace V V)).toElementMap s)).toElementMap x)
          ((toApproxMap W).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x))) := by
  rw [mapBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

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

theorem push_head_tail (z : (iterSys V).Element) :
    (push V).toElementMap (pair ((head V).toElementMap z) ((tail V).toElementMap z)) = z := by
  rw [head, tail, toElementMap_comp, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    pair_fst_snd, push, fold_unfold]

theorem unfold_fold (p : (prod V (iterSys V)).Element) :
    (unfold V).toElementMap ((fold V).toElementMap p) = p := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply]

theorem head_push (x : V.Element) (s : (iterSys V).Element) :
    (head V).toElementMap ((push V).toElementMap (pair x s)) = x := by
  rw [head, toElementMap_comp, push, unfold_fold, toElementMap_proj₀, fst_pair]

theorem tail_push (x : V.Element) (s : (iterSys V).Element) :
    (tail V).toElementMap ((push V).toElementMap (pair x s)) = s := by
  rw [tail, toElementMap_comp, push, unfold_fold, toElementMap_proj₁, snd_pair]

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

end DomainTheory.NeighbourhoodSystems.Exercise511
end
