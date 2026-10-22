module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Zcomb_app (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => Z n f x) :=
  beta (Zcomb_map_isScottContinuous n) f

end DomainTheory.DataTypesAsLattices
