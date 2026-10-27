module

public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.HF
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app


@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem HF_app2 (H e t : Pomega) :
    funOf (funOf (HF H) e) t = Hstep H e t := by
  rw [HF_app]
  exact beta (Hstep.isScottContinuous_t H e) t

end DomainTheory.DataTypesAsLattices
