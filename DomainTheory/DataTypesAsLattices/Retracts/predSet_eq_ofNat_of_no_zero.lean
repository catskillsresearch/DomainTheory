/-ai
If a set omits zero and its predecessor set is the singleton of k, then the set is the singleton of k + 1.

An element of the set is nonzero, hence a successor t + 1, and t belongs to the predecessor set, so t equals k. Conversely, k belongs to the predecessor set, so k + 1 belongs to the set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem predSet_eq_ofNat_of_no_zero {u : Pomega} {k : ℕ}
    (h0 : 0 ∉ u) (hk : predSet u = ofNat k) :
    u = ofNat (k + 1) := by
  ext m
  constructor
  · intro hm
    have hm0 : m ≠ 0 := fun h => h0 (by simpa [h] using hm)
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have : t ∈ predSet u := hm
    have : t = k := by
      have : t ∈ ofNat k := by rwa [hk] at this
      simpa [ofNat] using this
    simp [ofNat, this]
  · intro hm
    simp [ofNat] at hm
    subst hm
    have : k ∈ predSet u := by
      rw [hk]; simp [ofNat]
    exact this

end DomainTheory.DataTypesAsLattices
