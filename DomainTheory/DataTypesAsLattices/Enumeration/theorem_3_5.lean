module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ_app
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ_isRE
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_5_case2
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_5_case1

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






























/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability).**
If a total extensional mapping `p` is LAMBDA-definable, then there is a
LAMBDA-definable `q` with `val(p n) = q(val n)`. -/
theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : IsExtensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by
  obtain ⟨u, hu, hr⟩ := hp
  refine ⟨myhillQ valNat p, IsRE.combinatory (myhillQ_isRE hu hr), fun n => ?_⟩
  rw [myhillQ_app]
  ext k
  constructor
  · intro hk
    by_contra hnin
    have hinf : ∀ j, e j = valNat n → False := by
      intro j hj
      have : k ∈ valNat (p (fin j)) := by
        have := hext n (fin j) (by simp [valNat_fin, hj])
        simpa [this, valNat_fin] using hk
      exact hnin (Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨by simp [hj], this⟩⟩)
    -- Case 1: `val n` is infinite; finished after the filter construction.
    have hfin : ¬(valNat n).Finite := by
      intro hf
      obtain ⟨j, hj⟩ := exists_code_of_finite hf
      exact hinf j hj
    have hnin' : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)) := by
      intro ⟨j, hj, hkj⟩
      exact hnin (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hkj⟩⟩)
    exact theorem_3_5_case1 hu hr hext hk hnin' hfin
  · intro hk
    obtain ⟨j, hk⟩ := Set.mem_iUnion.mp hk
    obtain ⟨hj, hk⟩ := Set.mem_iUnion.mp hk
    by_contra hnin
    have hne : e j ≠ valNat n := by
      intro hj'
      have := hext n (fin j) (by simp [valNat_fin, hj'])
      exact hnin (by simpa [this, valNat_fin] using hk)
    exact theorem_3_5_case2 hu hr hext hj hne hk hnin

end DomainTheory.DataTypesAsLattices
