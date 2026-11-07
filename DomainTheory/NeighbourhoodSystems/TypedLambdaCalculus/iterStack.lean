module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.iterSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

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

theorem component_tail (z : (iterSys V).Element) (n : ℕ) :
    component ((tail V).toElementMap z) n = component z (n + 1) := by
  rw [tail_apply, component_ofSeq]

theorem fold_unfold (z : (iterSys V).Element) :
    (fold V).toElementMap ((unfold V).toElementMap z) = z := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply]

theorem unfold_fold (p : (prod V (iterSys V)).Element) :
    (unfold V).toElementMap ((fold V).toElementMap p) = p := by
  rw [unfold, fold, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply]

theorem push_head_tail (z : (iterSys V).Element) :
    (push V).toElementMap (pair ((head V).toElementMap z) ((tail V).toElementMap z)) = z := by
  rw [head, tail, toElementMap_comp, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    pair_fst_snd, push, fold_unfold]

theorem head_push (x : V.Element) (s : (iterSys V).Element) :
    (head V).toElementMap ((push V).toElementMap (pair x s)) = x := by
  rw [head, toElementMap_comp, push, unfold_fold, toElementMap_proj₀, fst_pair]

theorem tail_push (x : V.Element) (s : (iterSys V).Element) :
    (tail V).toElementMap ((push V).toElementMap (pair x s)) = s := by
  rw [tail, toElementMap_comp, push, unfold_fold, toElementMap_proj₁, snd_pair]

end
end DomainTheory.NeighbourhoodSystems
