/-ai
Every enumerated set is a neighbourhood of the section domain.

Proceed by strong induction on the index. At 0 the value is the master neighbourhood. A positive index is odd, of the form 2n+1, or even, of the form 2n+2, according to its remainder modulo 2. The odd value is the zero embedding of an enumerated neighbourhood of the underlying domain. The even value is the paired embedding of two earlier enumerated sets, which are neighbourhoods by the inductive hypothesis, because each component of the unpairing is strictly smaller than the index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.unpair_fst_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Every `V k` is a neighbourhood of `D^§`. -/
theorem Vsharp_mem (k : ℕ) : MemS D (Vsharp D P k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Vsharp_zero]; exact MemS.gamma
    · -- `k ≥ 1` is odd `2n+1` or even `2n+2`, decided choice-free by `k % 2`.
      rcases (by
        rcases Nat.lt_or_ge (k % 2) 1 with h | h
        · exact Or.inr ⟨k / 2 - 1, by omega⟩
        · exact Or.inl ⟨k / 2, by omega⟩ :
          (∃ n, k = 2 * n + 1) ∨ (∃ n, k = 2 * n + 2)) with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · rw [Vsharp_odd]; exact MemS.zero (P.mem_X n)
      · rw [Vsharp_even]
        exact MemS.pair (ih _ (by have := unpair_fst_le n; omega))
          (ih _ (by have := unpair_snd_le n; omega))

end Proposition77

end DomainTheory.NeighbourhoodSystems
