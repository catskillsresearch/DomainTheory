module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecu2082_finAux

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_fin : Primrec fin := by
  unfold fin
  exact primrec₂_finAux.comp
    (Primrec.pair Primrec.id (Primrec.succ.comp Primrec.id))

end DomainTheory.DataTypesAsLattices
