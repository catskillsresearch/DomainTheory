module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Scomb_app2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_app]
  exact beta (Scomb_mid_isScottContinuous f) g

end DomainTheory.DataTypesAsLattices
