module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.theorem_1_1
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.exists_index_of_finset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem chain_lemma {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    f (⋃ n, xs n) = ⋃ n, f (xs n) := by
  apply subset_antisymm
  · intro k hk
    have hchar := (theorem_1_1 f).mp hf (⋃ n, xs n) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (⋃ n, xs n) := by
      simp [e_pow2, Set.singleton_subset_iff, hk]
    obtain ⟨m, hm, hkm⟩ := hchar.mp hfin
    have hwit : ∀ i ∈ e m, ∃ n, i ∈ xs n := by
      intro i hi
      obtain ⟨n, hix⟩ := Set.mem_iUnion.mp (hm hi)
      exact ⟨n, hix⟩
    obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
    obtain ⟨N, hN⟩ := exists_index_of_finset xs hmono s (fun i hi =>
      hwit i (by
        have : i ∈ (s : Set ℕ) := hi
        rwa [hs] at this))
    have hem : e m ⊆ xs N := by rwa [← hs]
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    have : e (2 ^ k) ⊆ f (xs N) :=
      subset_trans hkm (IsScottContinuous.monotone hf hem)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact IsScottContinuous.monotone hf (Set.subset_iUnion xs n) hkn

end DomainTheory.DataTypesAsLattices
