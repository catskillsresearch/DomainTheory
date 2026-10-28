module
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Topology.Bases

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

namespace funOf

theorem monotone_left {u v : Pomega} (h : u ⊆ v) (x : Pomega) :
    funOf u x ⊆ funOf v x := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, hn, h hp⟩

theorem monotone_right (u : Pomega) {x y : Pomega} (h : x ⊆ y) :
    funOf u x ⊆ funOf u y := by
  intro m hm
  obtain ⟨n, hn, hp⟩ := hm
  exact ⟨n, subset_trans hn h, hp⟩

theorem bot (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

theorem iUnion (xs : ℕ → Pomega) (x : Pomega) :
    funOf (⋃ n, xs n) x = ⋃ n, funOf (xs n) x := by
  ext m
  constructor
  · intro ⟨n, hn, hk⟩
    obtain ⟨k, hmem⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k, ⟨n, hn, hmem⟩⟩
  · intro hm
    obtain ⟨k, ⟨n, hn, hmem⟩⟩ := Set.mem_iUnion.mp hm
    exact ⟨n, hn, Set.mem_iUnion.mpr ⟨k, hmem⟩⟩

theorem isScottContinuous (u : Pomega) : IsScottContinuous (funOf u) := by
  constructor
  intro x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    exact mem_scottUnion.mpr ⟨n, hn, ⟨n, subset_rfl, hp⟩⟩
  · intro hm
    obtain ⟨n, hn, ⟨k, hk, hp⟩⟩ := mem_scottUnion.mp hm
    exact ⟨k, subset_trans hk hn, hp⟩

theorem isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun u => funOf u y) := by
  constructor
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair n m, ?_, ⟨n, hn, ?_⟩⟩
    · simp [e_pow2, Set.singleton_subset_iff, hp]
    · simp [e_pow2]
  · intro hm
    obtain ⟨k, hk, n, hn, hp⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hp⟩

theorem diag_iUnion (d : Pomega) :
    funOf d d = ⋃ l, {m | e l ⊆ d ∧ m ∈ funOf (e l) (e l)} := by
  have h := theorem_1_3.diag (x := d)
    (f := fun u y => funOf u y)
    (fun y => isScottContinuous_left y)
    (fun u => isScottContinuous u)
  exact h

end funOf

end DomainTheory.DataTypesAsLattices
