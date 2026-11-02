module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem predSet_ofNat_zero : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem, Set.mem_singleton_iff]

end DomainTheory.DataTypesAsLattices
