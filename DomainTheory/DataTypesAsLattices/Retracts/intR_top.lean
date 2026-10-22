module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intR_top_of_nonsingleton

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_top : funOf intR topElem = topElem :=
  intR_top_of_nonsingleton 0 topElem (Set.mem_univ 0)
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

end DomainTheory.DataTypesAsLattices
