module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
import Mathlib.Data.Set.Insert

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

@[simp] theorem mem_ofNat {n k : ℕ} : k ∈ ofNat n ↔ k = n := by
  simp [ofNat, Set.mem_singleton_iff]

end DomainTheory.DataTypesAsLattices
