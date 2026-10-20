module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
























theorem Zcomb_app_isGraph (n : ℕ) (f : Pomega) :
    funOf (Zcomb n) f = graph (fun x => funOf (funOf (Zcomb n) f) x) := by
  rw [Zcomb_app]
  apply graph_ext
  intro x
  exact (beta (Z_isScottContinuous_right n f) x).symm

end DomainTheory.DataTypesAsLattices
