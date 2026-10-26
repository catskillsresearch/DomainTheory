module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_fixed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hfun_app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) Hfun_fixed
  simpa [HF_app2] using h.symm

end DomainTheory.DataTypesAsLattices
