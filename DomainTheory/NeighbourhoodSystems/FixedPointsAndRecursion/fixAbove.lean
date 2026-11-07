module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.iSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

def iterFrom (f : ApproximableMap V V) (a : V.Element) (n : ℕ) : V.Element :=
  (f.toElementMap)^[n] a

@[simp] theorem iterFrom_zero (f : ApproximableMap V V) (a : V.Element) :
    f.iterFrom a 0 = a := rfl

theorem iterFrom_succ (f : ApproximableMap V V) (a : V.Element) (n : ℕ) :
    f.iterFrom a (n + 1) = f.toElementMap (f.iterFrom a n) := by
  rw [iterFrom, iterFrom, Function.iterate_succ', Function.comp_apply]

theorem iterFrom_step (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    (n : ℕ) : f.iterFrom a n ≤ f.iterFrom a (n + 1) := by
  induction n with
  | zero => rw [iterFrom_succ f a 0, iterFrom_zero]; exact ha
  | succ k ih =>
    rw [iterFrom_succ f a k, iterFrom_succ f a (k + 1)]
    exact f.toElementMap_mono ih

theorem iterFrom_mono (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {n m : ℕ} (hnm : n ≤ m) : f.iterFrom a n ≤ f.iterFrom a m := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (iterFrom_step f ha _)

def fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) : V.Element :=
  NeighborhoodSystem.iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩)

theorem fixAbove_isFixed (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    f.toElementMap (f.fixAbove ha) = f.fixAbove ha := by
  let hdir : ∀ i j, ∃ k, f.iterFrom a i ≤ f.iterFrom a k ∧ f.iterFrom a j ≤ f.iterFrom a k :=
    fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩
  apply le_antisymm
  ·
    rw [fixAbove, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    have : f.toElementMap (f.iterFrom a n) = f.iterFrom a (n + 1) := (iterFrom_succ f a n).symm
    rw [this]
    exact NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir (n + 1)
  ·
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterFrom a n
        ≤ f.iterFrom a (n + 1) := iterFrom_mono f ha (Nat.le_succ n)
      _ = f.toElementMap (f.iterFrom a n) := iterFrom_succ f a n
      _ ≤ f.toElementMap (f.fixAbove ha) :=
          f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir n)

theorem fixAbove_least (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {z : V.Element} (haz : a ≤ z) (hz : f.toElementMap z ≤ z) : f.fixAbove ha ≤ z := by
  apply NeighborhoodSystem.iSupDirected_le
  intro n
  induction n with
  | zero => rwa [iterFrom_zero]
  | succ k ih =>
    rw [iterFrom_succ]
    exact le_trans (f.toElementMap_mono ih) hz

theorem le_fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    a ≤ f.fixAbove ha := by
  have := NeighborhoodSystem.le_iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩) 0
  rwa [iterFrom_zero] at this

end ApproximableMap
end
end DomainTheory.NeighbourhoodSystems
