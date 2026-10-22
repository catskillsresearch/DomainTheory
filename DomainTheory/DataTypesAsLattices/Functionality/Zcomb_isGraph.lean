module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Zcomb_isGraph (n : ℕ) :
    Zcomb n = graph (fun f => funOf (Zcomb n) f) := by
  apply graph_ext
  intro f
  rw [Zcomb_app]

end DomainTheory.DataTypesAsLattices
