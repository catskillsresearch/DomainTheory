
module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem plusR_typed_inr {a b y : Pomega} (hy : typed y b) :
    typed (pairSeq (ofNat 1) y) (plusR a b) := by
  rw [typed, plusR_app.app, pairSeq_app_zero, pairSeq_app_one, dcondSet.ofNat_one,
    ← hy]

end DomainTheory.DataTypesAsLattices
