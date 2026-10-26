module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem dcondSet_bool_idem (u : Pomega) :
    dcondSet (dcondSet u (ofNat 0) (ofNat 1)) (ofNat 0) (ofNat 1) =
      dcondSet u (ofNat 0) (ofNat 1) := by
  rcases dcondSet.cases u with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, dcondSet.ofNat_zero]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, dcondSet.ofNat_one]
  · rw [dcondSet.of_mixed h.1 h.2, dcondSet.top]
  · rw [dcondSet.of_empty h.1 h.2, dcondSet.bot]

end DomainTheory.DataTypesAsLattices
