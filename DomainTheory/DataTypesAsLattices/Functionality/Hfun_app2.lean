/-ai
Applying the raw fixed point first to an environment and then to a term yields one step of that fixed point.

Congruence of double application along the fixed-point equation for HF, rewritten by the double application of HF.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.HF_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun_fixed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hfun_app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) Hfun_fixed
  simpa [HF_app2] using h.symm

end DomainTheory.DataTypesAsLattices
