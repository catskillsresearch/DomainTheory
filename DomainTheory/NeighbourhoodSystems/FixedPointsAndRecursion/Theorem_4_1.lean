module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_8

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap

def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

@[simp] theorem iterMap_zero (f : ApproximableMap V V) : f.iterMap 0 = idMap V := rfl

@[simp] theorem iterMap_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterMap (n + 1) = f.comp (f.iterMap n) := rfl

theorem comp_mono {f g a b : ApproximableMap V V} (hfg : f ≤ g) (hab : a ≤ b) :
    f.comp a ≤ g.comp b := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hab X Y hXY, hfg Y Z hYZ⟩

theorem iterMap_mono_map {f g : ApproximableMap V V} (hfg : f ≤ g) (n : ℕ) :
    f.iterMap n ≤ g.iterMap n := by
  induction n with
  | zero => show (idMap V) ≤ (idMap V); exact le_refl _
  | succ k ih => exact comp_mono hfg ih

theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

@[simp] theorem mem_fixElement (f : ApproximableMap V V) {X : Set α} :
    f.fixElement.mem X ↔ ∃ n, (f.iterMap n).rel V.master X := Iff.rfl

theorem fixElement_mono {f g : ApproximableMap V V} (hfg : f ≤ g) :
    f.fixElement ≤ g.fixElement := by
  rintro X ⟨n, hn⟩
  exact ⟨n, iterMap_mono_map hfg n V.master X hn⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
end
