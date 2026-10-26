module

public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_same_ofNat
public import DomainTheory.DataTypesAsLattices.Retracts.predSet_eq_ofNat_of_no_zero

public import DomainTheory.DataTypesAsLattices.Lambda.predSet_ofNat_succ
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_mixed
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_top
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace intR

theorem app_ofNat : ∀ n, funOf intR (ofNat n) = ofNat n
  | 0 => by
    rw [app, dcondSet_ofNat_zero]
  | n + 1 => by
    rw [app, predSet_ofNat_succ, app_ofNat n, dcondSet_same_ofNat,
      dcondSet_ofNat_succ]

theorem top_of_nonsingleton :
    ∀ n u, n ∈ u → (∀ k ∈ u, n ≤ k) → u ≠ botElem → (∀ k, u ≠ ofNat k) →
      funOf intR u = topElem := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u hn hmin hne hns
    rw [app]
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

theorem top : funOf intR topElem = topElem :=
  top_of_nonsingleton 0 topElem (Set.mem_univ 0)
    (fun _ _ => Nat.zero_le _)
    (by
      intro h
      have : (0 : ℕ) ∈ (botElem : Pomega) := by
        rw [← h]
        exact Set.mem_univ 0
      simp [botElem] at this)
    (fun n h => by
      have h0 : (0 : ℕ) ∈ ofNat n := by
        have : (0 : ℕ) ∈ topElem := Set.mem_univ 0
        rwa [h] at this
      have h1 : (1 : ℕ) ∈ ofNat n := by
        have : (1 : ℕ) ∈ topElem := Set.mem_univ 1
        rwa [h] at this
      simp [ofNat] at h0 h1
      omega)

theorem idem (x : Pomega) : funOf intR (funOf intR x) = funOf intR x := by
  by_cases hbot : x = botElem
  · subst hbot
    rw [bot, bot]
  · by_cases hsing : ∃ n, x = ofNat n
    · obtain ⟨n, rfl⟩ := hsing
      rw [app_ofNat, app_ofNat]
    · have hx : funOf intR x = topElem := by
        have hne : x.Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        exact top_of_nonsingleton (sInf x) x (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun n hn => hsing ⟨n, hn⟩)
      rw [hx, top]

theorem isGraph : intR = graph (funOf intR) := by
  refine eq_intF.symm.trans ?_
  apply graph_ext
  intro u
  exact (app u).symm

theorem isRetract : Retract intR := by
  constructor
  change intR = graph (fun x => funOf intR (funOf intR x))
  refine isGraph.trans ?_
  apply graph_ext
  intro x
  exact (idem x).symm

end intR

end DomainTheory.DataTypesAsLattices
