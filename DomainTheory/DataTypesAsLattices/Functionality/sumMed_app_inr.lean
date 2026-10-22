
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_fst
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_snd
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_app_inr (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 1) x) = funOf g x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_one]

end DomainTheory.DataTypesAsLattices
