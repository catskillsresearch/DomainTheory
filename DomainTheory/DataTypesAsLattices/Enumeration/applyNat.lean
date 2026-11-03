module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def applyNat (n m : ℕ) : ℕ := pair n m + 1

noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1

noncomputable def argNat (k : ℕ) : ℕ := (unpair k).2

theorem eq_3_5 (n m : ℕ) : opNat (pair n m) = n := by simp [opNat, unpair_pair]

theorem eq_3_6 (n m : ℕ) : argNat (pair n m) = m := by simp [argNat, unpair_pair]

theorem eq_3_8_apply : applyNat 0 0 = 1 := by simp [applyNat, pair]

theorem eq_3_9_apply : applyNat 0 1 = 3 := by simp [applyNat, pair]

theorem eq_3_10_apply : applyNat 3 1 = 12 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
