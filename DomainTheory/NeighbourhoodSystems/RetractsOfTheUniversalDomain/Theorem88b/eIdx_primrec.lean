module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem eIdx_primrec : Nat.Primrec (eIdx P) := by
  have hc0 : Nat.Primrec (fun n => isZero n) := primrec_isZero
  have hcm : Nat.Primrec (fun n : ℕ => isZero ((n - P.masterIdx) + (P.masterIdx - n))) :=
    primrec_isZero.comp
      (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const P.masterIdx))
        (primrec_sub₂ (Nat.Primrec.const P.masterIdx) primrec_id))
  have hinner : Nat.Primrec (fun n : ℕ =>
      selectFn (isZero ((n - P.masterIdx) + (P.masterIdx - n))) 0 n) :=
    primrec_ite hcm (Nat.Primrec.const 0) primrec_id
  refine (primrec_ite hc0 (Nat.Primrec.const P.masterIdx) hinner).of_eq (fun n => ?_)
  rcases (show isZero n = 0 ∨ isZero n = 1 from by have := isZero_le_one n; omega) with h0 | h0
  · rw [h0, selectFn_zero]
    have hn0 : n ≠ 0 := by intro h; subst h; unfold isZero at h0; omega
    rcases (show isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 0 ∨
        isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 1 from
        by have := isZero_le_one ((n - P.masterIdx) + (P.masterIdx - n)); omega) with h1 | h1
    · rw [h1, selectFn_zero]
      have hnm : n ≠ P.masterIdx := by intro h; subst h; unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_right hnm]
    · rw [h1, selectFn_one]
      have hnm : n = P.masterIdx := by unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_left hnm]
  · rw [h0, selectFn_one]
    have hn0 : n = 0 := by unfold isZero at h0; omega
    unfold eIdx
    rw [ite_eq_left hn0]

end DomainTheory.NeighbourhoodSystems
