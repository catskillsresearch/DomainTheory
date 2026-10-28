module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_14
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

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

@[simp] theorem kpow_succ (z : Set S) (n : ℕ) : kpow z (n + 1) = z * kpow z n := rfl

def G (z v : Set S) (w : Set S) : Set S := z * w ∪ v

def star (z : Set S) : Set S := {s | ∃ n, s ∈ kpow z n}

def parkA (a b : Set S) : Set S := a ∪ b * star a * b

def parkC (a b c d : Set S) : Set S := c ∪ b * star a * d

def parkX (a b c d : Set S) : Set S := star (parkA a b) * parkC a b c d

def parkY (a b c d : Set S) : Set S := star a * (b * parkX a b c d ∪ d)

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

theorem mem_star {z : Set S} {s : S} : s ∈ star z ↔ ∃ n, s ∈ kpow z n := Iff.rfl

theorem mem_star_singleton (e s : S) : s ∈ star ({e} : Set S) ↔ ∃ n, s = e ^ n := by
  rw [mem_star]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_kpow_singleton e s n).mp hn⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (mem_kpow_singleton e (e ^ n) n).mpr rfl⟩

theorem smul_assoc (a b c : Set S) : a * b * c = a * (b * c) := by
  ext s; simp only [Set.mem_mul]
  constructor
  · rintro ⟨u, ⟨p, hp, q, hq, rfl⟩, w, hw, rfl⟩
    exact ⟨p, hp, q * w, ⟨q, hq, w, hw, rfl⟩, by rw [mul_assoc]⟩
  · rintro ⟨p, hp, u, ⟨q, hq, w, hw, rfl⟩, rfl⟩
    exact ⟨p * q, ⟨p, hp, q, hq, rfl⟩, w, hw, by rw [mul_assoc]⟩

theorem smul_union (a b c : Set S) : a * (b ∪ c) = a * b ∪ a * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, hu, w, (hw | hw), rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, hu, w, Or.inl hw, rfl⟩
    · exact ⟨u, hu, w, Or.inr hw, rfl⟩

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

theorem sunion_mul (a b c : Set S) : (a ∪ b) * c = a * c ∪ b * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, (hu | hu), w, hw, rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, Or.inl hu, w, hw, rfl⟩
    · exact ⟨u, Or.inr hu, w, hw, rfl⟩

theorem star_mul_isFixed (z v : Set S) : z * (star z * v) ∪ v = star z * v := by
  conv_rhs => rw [star_eq z]
  rw [sunion_mul, one_mul, smul_assoc]
  exact Set.union_comm _ _

theorem arden (z v : Set S) : lfpSet (G z v) = star z * v := by
  apply Set.Subset.antisymm
  · exact lfpSet_least (G z v) (star_mul_isFixed z v)
  · intro s hs x hx
    exact star_mul_subset_prefixed z v x hx hs

theorem parkX_eq (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c := by
  have hfix : parkA a b * parkX a b c d ∪ parkC a b c d = parkX a b c d :=
    star_mul_isFixed (parkA a b) (parkC a b c d)
  conv_lhs => rw [← hfix]
  simp only [parkA, parkC, parkY, sunion_mul, smul_union, smul_assoc,
    Set.union_comm, Set.union_left_comm]

theorem parkY_eq (a b c d : Set S) :
    parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d := by
  have hfix : a * parkY a b c d ∪ (b * parkX a b c d ∪ d) = parkY a b c d :=
    star_mul_isFixed a (b * parkX a b c d ∪ d)
  conv_lhs => rw [← hfix]
  simp only [Set.union_assoc, Set.union_comm]

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

  have hpre : a * y ∪ (b * x ∪ d) ⊆ y := Set.union_subset hay (Set.union_subset hbx hdy)
  have hyy : star a * (b * x ∪ d) ⊆ y := by
    rw [← arden a (b * x ∪ d)]
    exact lfpSet_subset (G a (b * x ∪ d)) hpre

  have key : b * star a * b * x ∪ b * star a * d = b * (star a * (b * x ∪ d)) := by
    simp only [smul_assoc, smul_union]

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

theorem park_solves (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
      parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d :=
  ⟨parkX_eq a b c d, parkY_eq a b c d⟩

theorem part1 (e e' : S) :
    lfpSet (fun w => ({e} : Set S) * w ∪ {e'}) = star ({e} : Set S) * {e'} := by
  have hG : (fun w => ({e} : Set S) * w ∪ {e'}) = G ({e} : Set S) {e'} := rfl
  rw [hG]; exact arden {e} {e'}

end

section
variable {S : Type*} [Monoid S]

theorem part1_freeMonoid (e e' : FreeMonoid Bool) :
    lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'})
      = star ({e} : Set (FreeMonoid Bool)) * {e'} :=
  part1 e e'
end

end DomainTheory.NeighbourhoodSystems.Exercise515
end
