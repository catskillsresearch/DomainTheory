module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_tag2 (H x t : Pomega) :
    Hstep H (tagInj 2 x) t = hSucc H (tagInj 2 x) t := by
  simp only [Hstep, expTag, tagInj_zero, predSet_ofNat_succ,
    dcondSet_ofNat_succ, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
