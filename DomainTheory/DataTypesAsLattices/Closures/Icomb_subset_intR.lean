
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, §5.** `int` is a closure: `I ⊆ int = int ∘ int`. -/
theorem Icomb_subset_intR : Icomb ⊆ intR := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : e n ⊆ funOf intR (e n) := by
    by_cases hbot : e n = botElem
    · rw [hbot, intR.bot]
    · by_cases hsing : ∃ k, e n = ofNat k
      · obtain ⟨k, hk⟩ := hsing
        rw [hk, intR.app_ofNat]
      · have hne : (e n).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        rw [intR.top_of_nonsingleton (sInf (e n)) (e n) (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun k hk => hsing ⟨k, hk⟩)]
        exact fun _ _ => Set.mem_univ _
  rw [intR.isGraph]
  exact ⟨n, m, rfl, hsub hm⟩

end DomainTheory.DataTypesAsLattices
