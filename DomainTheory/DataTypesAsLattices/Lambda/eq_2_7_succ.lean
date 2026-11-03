module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_7_succ (x y : Pomega) (k : ℕ) :
    condSet (ofNat (k + 1)) x y = y := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
