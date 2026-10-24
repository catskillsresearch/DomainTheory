module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.DiagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStepCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.diagFixed_masterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStep_diagFixed_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_diagFixed_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFoldCode_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.primrec_myStepCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.primrec_myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.diagFixed_myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.myFoldl_subset

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}


/-- **The key lemma.** Refolding a list `l` from a start `n` that is `⊆` (in `P.X`) another start
`r`, reproduces `P.X n ∩ P.X (fold of l from r)` — *provided* this is already known to be
`V`-consistent at the end (i.e. `∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl … r)`). No `a`/`DiagFixed`
apparatus is needed: this is a purely structural fact about `myStep`'s consistency gate. -/
theorem myFoldl_inter_of_le
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) {n r : ℕ}, P.X n ⊆ P.X r →
      (∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl (myStep P qChar cons) r)) →
      P.X (l.foldl (myStep P qChar cons) n) = P.X n ∩ P.X (l.foldl (myStep P qChar cons) r) := by
  intro l
  induction l with
  | nil =>
    intro n r hnr _
    simp only [List.foldl_nil]
    exact (Set.inter_eq_left.mpr hnr).symm
  | cons e rest ih =>
    intro n r hnr hk
    simp only [List.foldl_cons] at hk ⊢
    have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
      by_cases hq : (qChar e) = 1
      · exact Or.inr hq
      · exact Or.inl hq
    rcases hq_dec with hq | hq
    · have hstepR : myStep P qChar cons r e = r := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      have hstepN : myStep P qChar cons n e = n := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      rw [hstepR] at hk ⊢
      rw [hstepN]
      exact ih hnr hk
    · have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
        by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
        · exact Or.inr hc
        · exact Or.inl hc
      rcases hc_dec with hc | hc
      · have hstepR : myStep P qChar cons r e = r := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hc, selectFn_zero]
        have hcN : cons (Nat.pair n e.unpair.2) ≠ 1 := by
          intro hcn
          obtain ⟨w, hw⟩ := (hcons n e.unpair.2).mp hcn
          exact hc ((hcons r e.unpair.2).mpr
            ⟨w, hw.trans (Set.inter_subset_inter_left _ hnr)⟩)
        have hstepN : myStep P qChar cons n e = n := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hcN, selectFn_zero]
        rw [hstepR] at hk ⊢
        rw [hstepN]
        exact ih hnr hk
      · obtain ⟨w0, hw0⟩ := (hcons r e.unpair.2).mp hc
        have hstepR : myStep P qChar cons r e = P.inter r e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hc, selectFn_one]
        rw [hstepR] at hk ⊢
        obtain ⟨k, hkk⟩ := hk
        have hYsub : P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2))
            ⊆ P.X e.unpair.2 := by
          refine (myFoldl_subset hcons rest (P.inter r e.unpair.2)).trans ?_
          rw [P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_right
        have hkR : P.X k ⊆ P.X n := hkk.trans Set.inter_subset_left
        have hkY : P.X k ⊆ P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) :=
          hkk.trans Set.inter_subset_right
        have hkne : P.X k ⊆ P.X e.unpair.2 := hkY.trans hYsub
        have hwitN : ∃ k, P.X k ⊆ P.X n ∩ P.X e.unpair.2 := ⟨k, Set.subset_inter hkR hkne⟩
        have hcN : cons (Nat.pair n e.unpair.2) = 1 := (hcons n e.unpair.2).mpr hwitN
        have hstepN : myStep P qChar cons n e = P.inter n e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hcN, selectFn_one]
        rw [hstepN]
        have hnr' : P.X (P.inter n e.unpair.2) ⊆ P.X (P.inter r e.unpair.2) := by
          rw [P.inter_spec hwitN, P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_inter_left _ hnr
        have hk' : ∃ k', P.X k' ⊆ P.X (P.inter n e.unpair.2) ∩
            P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) := by
          refine ⟨k, ?_⟩
          rw [P.inter_spec hwitN]
          exact Set.subset_inter (Set.subset_inter hkR hkne) hkY
        rw [ih hnr' hk', P.inter_spec hwitN, Set.inter_assoc, Set.inter_eq_right.mpr hYsub]

end DomainTheory.NeighbourhoodSystems
