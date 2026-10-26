module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.predSet_union
public import DomainTheory.DataTypesAsLattices.Closures.predSet_succSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** Shift used in the sum of closures. -/
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))

namespace boxShift

theorem map_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => ofNat 0 ∪ succSet (funOf a (predSet x))) :=
  theorem_1_3 (union_const_left_isScottContinuous (ofNat 0))
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous a) predSet_isScottContinuous))

theorem app (a x : Pomega) :
    funOf (boxShift a) x = ofNat 0 ∪ succSet (funOf a (predSet x)) :=
  beta (map_isScottContinuous a) x

theorem expansive {a : Pomega} (ha : Closure a) (x : Pomega) :
    x ⊆ funOf (boxShift a) x := by
  rw [app]
  intro k hk
  cases k with
  | zero => exact Or.inl rfl
  | succ k =>
    refine Or.inr ⟨k, ?_, rfl⟩
    have hx : predSet x ⊆ funOf a (predSet x) := by
      have := funOf_monotone_left ha.out.1 (predSet x)
      rwa [Icomb.app] at this
    exact hx hk

theorem isRetract {a : Pomega} (ha : Retract a) :
    Retract (boxShift a) := by
  constructor
  change boxShift a =
    graph (fun x => funOf (boxShift a) (funOf (boxShift a) x))
  apply graph_ext
  intro x
  rw [app, app]
  have hpred : predSet (ofNat 0 ∪ succSet (funOf a (predSet x))) =
      funOf a (predSet x) := by
    rw [predSet_union, predSet_ofNat_zero, predSet_succSet]
    simp [botElem]
  rw [hpred, retract_app ha]

theorem zero_mem_app (a x : Pomega) : (0 : ℕ) ∈ funOf (boxShift a) x := by
  rw [app]
  exact Or.inl (by simp [ofNat])

theorem app_ne_bot (a x : Pomega) : funOf (boxShift a) x ≠ botElem := by
  intro h
  have h0 := zero_mem_app a x
  rw [h] at h0
  simp [botElem] at h0

end boxShift

end DomainTheory.DataTypesAsLattices
