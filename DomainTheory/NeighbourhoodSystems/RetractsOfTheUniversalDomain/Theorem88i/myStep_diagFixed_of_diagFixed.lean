module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)


variable {P qChar cons}

/-- **One-step preservation of `DiagFixed`.** If the accumulator `r` is already `DiagFixed` and
`e`'s gate succeeds (`qChar e = 1` giving `DiagFixed` of the raw index `e.unpair.2` via `hqChar`, and
`cons (Nat.pair r e.unpair.2) = 1` giving a `V`-consistency witness), then `myStep P qChar cons r e`
is `DiagFixed` too — via `fixedNbhd_subsystem a`'s `inter_closed` plus `P.inter_spec`. If the gate
fails, the step no-ops and the invariant is preserved trivially. -/
theorem myStep_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {r : ℕ} (hr : DiagFixed P a r) (e : ℕ) :
    DiagFixed P a (myStep P qChar cons r e) := by
  unfold myStep
  have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
    by_cases hq : (qChar e) = 1
    · exact Or.inr hq
    · exact Or.inl hq
  rcases hq_dec with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
    exact hr
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
      by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
      exact hr
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one]
      have hn : DiagFixed P a e.unpair.2 :=
        (hqChar e.unpair.2).mpr ⟨e.unpair.1, by rw [pair_unpair]; exact hq⟩
      obtain ⟨k, hk⟩ := (hcons r e.unpair.2).mp hc
      have hVinter : V.mem (P.X r ∩ P.X e.unpair.2) := by
        rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
      have hfix : (fixedNbhd a).mem (P.X r ∩ P.X e.unpair.2) :=
        (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a r).mp hr)
          ((diagFixed_iff_fixedNbhd_mem P a e.unpair.2).mp hn) hVinter
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]
      exact hfix

end DomainTheory.NeighbourhoodSystems
