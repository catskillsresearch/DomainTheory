/-ai
The identity combinator is contained in the integer retract. Scott's §5 records this containment as the expansiveness half of the statement that the integer retract is a closure.

A pair (n, m) in the identity has m in en, so it is enough that en be contained in the integer retract applied to en, after which the retract equals the graph of its own application. If en is ⊥, the retract fixes ⊥. If en is a singleton integer, the retract fixes that integer. Otherwise en is nonempty and not a singleton, so the retract sends it to ⊤, taking the least element of en as the witness, and en is contained in ⊤.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, §5.** `int` is a closure: `I ⊆ int = int ∘ int`. -/
theorem Icomb_subset_intR : Icomb ⊆ intR := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have hsub : e n ⊆ funOf intR (e n) := by
    by_cases hbot : e n = botElem
    · rw [hbot, intR_bot]
    · by_cases hsing : ∃ k, e n = ofNat k
      · obtain ⟨k, hk⟩ := hsing
        rw [hk, intR_ofNat]
      · have hne : (e n).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        rw [intR_top_of_nonsingleton (sInf (e n)) (e n) (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun k hk => hsing ⟨k, hk⟩)]
        exact fun _ _ => Set.mem_univ _
  rw [intR_isGraph]
  exact ⟨n, m, rfl, hsub hm⟩

end DomainTheory.DataTypesAsLattices
