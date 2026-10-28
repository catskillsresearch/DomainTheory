module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_7_succ (x y : Pomega) (k : ℕ) :
    condSet (ofNat (k + 1)) x y = y := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
