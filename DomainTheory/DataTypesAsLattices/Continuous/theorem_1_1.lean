/-ai
Scott 1976, Theorem 1.1, the characterization theorem: a map f is Scott continuous if and only if, for every x and every finite code m, the finite set coded by m is contained in f(x) exactly when some finite code n already has its finite set contained in x and the finite set coded by m contained in f of that finite set.

If f is Scott continuous and the finite set coded by m lies in f(x), each of its members lies in the Scott union, so is realized on some finite subset of x. Finiteness assembles those witnesses into one code. The opposite inclusion is monotonicity of f. Conversely, membership of k in f(x) is compared with membership in the Scott union by passing through the singleton finite set coded by 2^k and applying the stated finite-subset criterion in both directions.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_monotone
public import DomainTheory.DataTypesAsLattices.Continuous.exists_e_cover_finite

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Theorem 1.1 (The characterization theorem).**
`f` is continuous iff `e m ⊆ f(x)` just when some finite `e n ⊆ x` already
satisfies `e m ⊆ f(e n)`. -/
theorem theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by
  constructor
  · intro hf x m
    constructor
    · intro hmf
      have : ∀ k ∈ e m, ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
        intro k hk
        have : k ∈ scottUnion f x := by
          rw [← hf x]; exact hmf hk
        exact mem_scottUnion.mp this
      obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
      obtain ⟨N, hN, hsf⟩ := exists_e_cover_finite hf s (fun k hk =>
        this k (by
          have : k ∈ (s : Set ℕ) := hk
          rwa [hs] at this))
      exact ⟨N, hN, by simpa [hs] using hsf⟩
    · intro ⟨n, hn, hmf⟩
      exact subset_trans hmf (isScottContinuous_monotone hf hn)
  · intro h x
    ext k
    constructor
    · intro hk
      have : e (2 ^ k) ⊆ f x := by
        simp [e_pow2, Set.singleton_subset_iff, hk]
      obtain ⟨n, hn, hkn⟩ := (h x (2 ^ k)).mp this
      refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
      simpa [e_pow2, Set.singleton_subset_iff] using hkn
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e (2 ^ k) ⊆ f (e n) := by
        simp [e_pow2, Set.singleton_subset_iff, hkn]
      have : e (2 ^ k) ⊆ f x := (h x (2 ^ k)).mpr ⟨n, hn, this⟩
      simpa [e_pow2, Set.singleton_subset_iff] using this

end DomainTheory.DataTypesAsLattices
