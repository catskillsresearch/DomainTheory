module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app
public import DomainTheory.DataTypesAsLattices.Retracts.predSet_eq_ofNat_of_no_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































/-- **Scott 1976, after (4.7).** `int(u) = ⊤` when `u` is not `⊥` and not a
singleton integer. -/
theorem intR_top_of_nonsingleton :
    ∀ n u, n ∈ u → (∀ k ∈ u, n ≤ k) → u ≠ botElem → (∀ k, u ≠ ofNat k) →
      funOf intR u = topElem := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u hn hmin hne hns
    rw [intR_app]
    by_cases h0 : 0 ∈ u
    · have hp : ∃ t, t + 1 ∈ u := by
        by_contra hp
        apply hns 0
        ext m
        constructor
        · intro hm
          have : m = 0 := by
            by_contra hm0
            obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
            exact hp ⟨t, hm⟩
          simp [ofNat, this]
        · intro hm
          simpa [ofNat] using hm.symm ▸ h0
      rw [dcondSet_of_mixed h0 hp]
    · have hn0 : n ≠ 0 := fun h => h0 (by simpa [h] using hn)
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hn' : n' ∈ predSet u := hn
      have hmin' : ∀ k ∈ predSet u, n' ≤ k := by
        intro k hk
        have : n' + 1 ≤ k + 1 := hmin (k + 1) hk
        omega
      have hne' : predSet u ≠ botElem := by
        intro hempty
        have : n' ∈ predSet u := hn'
        rw [hempty] at this
        simp [botElem] at this
      have hns' : ∀ k, predSet u ≠ ofNat k := by
        intro k hk
        exact hns (k + 1) (predSet_eq_ofNat_of_no_zero h0 hk)
      have hpred : funOf intR (predSet u) = topElem :=
        ih n' (Nat.lt_succ_self n') (predSet u) hn' hmin' hne' hns'
      rw [hpred, dcondSet_top, dcondSet_of_pos_not_zero h0 ⟨n', hn⟩]

end DomainTheory.DataTypesAsLattices
