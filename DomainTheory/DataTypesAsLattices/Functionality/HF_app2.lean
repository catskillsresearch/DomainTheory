module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep_isScottContinuous_t
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem HF_app2 (H e t : Pomega) :
    funOf (funOf (HF H) e) t = Hstep H e t := by
  rw [HF_app]
  exact beta (Hstep_isScottContinuous_t H e) t

end DomainTheory.DataTypesAsLattices
