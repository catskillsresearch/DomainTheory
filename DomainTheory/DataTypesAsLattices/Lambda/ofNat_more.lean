module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.sucC_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace ofNat

theorem combinatory : ∀ n, IsCombinatory (ofNat n)
  | 0 => by
    simpa [zeroC] using IsCombinatory.zero
  | n + 1 => by
    have h := IsCombinatory.app IsCombinatory.suc (combinatory n)
    simpa [sucC.app, succSet.ofNat] using h

theorem zero_nonempty : (ofNat 0).Nonempty :=
  ⟨0, rfl⟩

theorem zero_not_pos : ¬ ∃ n, n + 1 ∈ ofNat 0 := by
  intro ⟨n, hn⟩
  simp [ofNat] at hn

end ofNat

namespace topElem

theorem ne_ofNat_zero : topElem ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by rw [← h]; exact Set.mem_univ 1
  simp [ofNat] at this

end topElem

end DomainTheory.DataTypesAsLattices

