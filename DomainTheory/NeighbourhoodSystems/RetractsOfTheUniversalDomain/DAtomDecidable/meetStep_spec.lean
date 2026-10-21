/-ai
If an accumulator has success bit at most one and describes a set, in the sense that success means its index set equals the set and failure means the set is empty, then one meet step at a further index describes the intersection of that set with the index set of the further index.

The success bit of the result is at most one. For both the success and the failure conclusions, split on whether the incoming success bit is zero or one. If it is zero, the step selects the failure code: the success conclusion is impossible, and the failure conclusion holds because the described set is empty. If it is one, split on whether the consistency function accepts the pair of the current index with the further index. Rejection selects failure, so success is impossible, and failure holds because a common member of the described set and the further index set would be a consistency witness. Acceptance selects the intersection index: success rewrites the index set of that intersection as the intersection of the two index sets and replaces the current index set by the described set, while failure is impossible.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetStep_ok_le_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)




/-- **One-step transfer of the meet-fold invariant**: if `init` codes `(ok, idx)` faithfully
relative to some set `S` (`ok = 1 → idxSet idx = S`, `ok = 0 → S = ∅`), then `meetStep init i`
codes the same relative to `S ∩ idxSet i` — the positive constraint contributed by `i`. -/
theorem meetStep_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {init : ℕ} {S : Set ℕ} (hle : init.unpair.1 ≤ 1)
    (h1 : init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S)
    (h0 : init.unpair.1 = 0 → S = ∅) (i : ℕ) :
    (meetStep P cons init i).unpair.1 ≤ 1 ∧
      ((meetStep P cons init i).unpair.1 = 1 →
        idxSet P.X (meetStep P cons init i).unpair.2 = S ∩ idxSet P.X i) ∧
      ((meetStep P cons init i).unpair.1 = 0 → S ∩ idxSet P.X i = ∅) := by
  refine ⟨meetStep_ok_le_one P cons init i, ?_, ?_⟩ <;>
    (unfold meetStep
     rcases (show init.unpair.1 = 0 ∨ init.unpair.1 = 1 by omega) with hi | hi)
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro h; exact absurd h (by decide)
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro h; exact absurd h (by decide)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_snd, unpair_pair_fst]
      intro _
      have heq : P.X init.unpair.2 ∩ P.X i = P.X (P.inter init.unpair.2 i) :=
        (P.inter_spec (hcons _ _ |>.mp hc)).symm
      rw [← idxSet_inter_of_inter_eq (e := P.X) heq, h1 hi]
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro _
    rw [h0 hi]; simp
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro _
      rw [← h1 hi]
      ext m
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hm1 hm2
      exact hc ((hcons _ _).mpr ⟨m, Set.subset_inter hm1 hm2⟩)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_fst]
      intro h; exact absurd h (by decide)

end DomainTheory.NeighbourhoodSystems
