module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

@[simp] theorem mem_tail {n m : ℕ} : m ∈ tail n ↔ n ≤ m := Iff.rfl

def mem (X : Set ℕ) : Prop := ∃ n, X = tail n

theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp only [Set.mem_inter_iff, mem_tail]
  omega

theorem tail_subset_iff {n m : ℕ} : tail n ⊆ tail m ↔ m ≤ n := by
  constructor
  · intro h
    exact h (show n ∈ tail n from le_refl n)
  · intro hmn k hk
    exact le_trans hmn hk

theorem nestedOrDisjoint : NestedOrDisjoint mem := by
  rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases le_total n m with h | h
  · exact Or.inr (Or.inl (tail_subset_iff.mpr h))
  · exact Or.inl (tail_subset_iff.mpr h)

def neighborhoodSystem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint mem (tail 0) ⟨0, Nat.zero_le 0⟩ ⟨0, rfl⟩ nestedOrDisjoint
    (fun {X} hX => by obtain ⟨n, rfl⟩ := hX; exact tail_subset_iff.mpr (Nat.zero_le n))

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ ∃ n, X = tail n := Iff.rfl

theorem mem_tail_nbhd (n : ℕ) : neighborhoodSystem.mem (tail n) := ⟨n, rfl⟩

def fin (n : ℕ) : neighborhoodSystem.Element := neighborhoodSystem.principal (mem_tail_nbhd n)

def top : neighborhoodSystem.Element where
  mem X := neighborhoodSystem.mem X
  sub h := h
  master_mem := neighborhoodSystem.master_mem
  inter_mem := by
    rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨max n m, tail_inter n m⟩
  up_mem _ hY _ := hY

@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

theorem element_eq (x : neighborhoodSystem.Element) :
    (∃ n, x = fin n) ∨ x = top := by
  classical
  by_cases h : ∀ n, x.mem (tail n)
  · refine Or.inr ?_
    apply Element.ext
    intro X
    constructor
    · intro hx; exact x.sub hx
    · rintro ⟨n, rfl⟩; exact h n
  · refine Or.inl ?_
    have h' : ∃ n, ¬ x.mem (tail n) := not_forall.mp h
    have hpos : ∀ n, ¬ x.mem (tail n) → 0 < n := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact absurd x.master_mem hn
      · exact hp
    have hspec : ¬ x.mem (tail (Nat.find h')) := Nat.find_spec h'
    have hmin : ∀ j, j < Nat.find h' → x.mem (tail j) := by
      intro j hj
      by_contra hc
      exact Nat.find_min h' hj hc
    have hn₀ : 0 < Nat.find h' := hpos _ hspec
    refine ⟨Nat.find h' - 1, ?_⟩
    apply Element.ext
    intro X
    have key : ∀ j, x.mem (tail j) ↔ j ≤ Nat.find h' - 1 := by
      intro j
      constructor
      · intro hj
        by_contra hc
        have hle : Nat.find h' ≤ j := by omega
        exact hspec (x.up_mem hj (mem_tail_nbhd (Nat.find h')) (tail_subset_iff.mpr hle))
      · intro hj
        exact hmin j (by omega)
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := x.sub hx
      exact ⟨mem_tail_nbhd j, tail_subset_iff.mpr ((key j).mp hx)⟩
    · rintro ⟨hX, hsub⟩
      obtain ⟨j, rfl⟩ := hX
      exact (key j).mpr (tail_subset_iff.mp hsub)

theorem fin_le_iff (n m : ℕ) : fin n ≤ fin m ↔ n ≤ m := by
  rw [fin, fin, neighborhoodSystem.principal_le_iff, tail_subset_iff]

theorem fin_strictMono : StrictMono fin := by
  intro n m hnm
  refine lt_of_le_of_ne ((fin_le_iff n m).mpr hnm.le) ?_
  intro heq
  have : m ≤ n := (fin_le_iff m n).mp (le_of_eq heq.symm)
  exact absurd (le_antisymm hnm.le this) (Nat.ne_of_lt hnm)

theorem le_top (x : neighborhoodSystem.Element) : x ≤ top :=
  fun _ hX => x.sub hX

theorem top_isTotal : neighborhoodSystem.IsTotal top :=
  fun y _ => le_top y

theorem isTotal_iff_top (x : neighborhoodSystem.Element) :
    neighborhoodSystem.IsTotal x ↔ x = top := by
  constructor
  · intro h
    exact le_antisymm (le_top x) (h top (le_top x))
  · rintro rfl; exact top_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise112
