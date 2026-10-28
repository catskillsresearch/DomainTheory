module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_6 : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
