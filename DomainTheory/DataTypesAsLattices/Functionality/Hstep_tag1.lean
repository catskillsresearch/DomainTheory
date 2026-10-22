module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
