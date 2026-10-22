module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep_tag6 (H x t : Pomega) :
    Hstep H (tagInj 6 x) t = hLam H (tagInj 6 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet_ofNat_succ,
    predSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    predSet_iterate_ofNat (k := 4) (i := 2),
    predSet_iterate_ofNat (k := 5) (i := 1),
    predSet_iterate_self, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
