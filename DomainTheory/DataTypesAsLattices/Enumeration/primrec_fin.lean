module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecu2082_finAux

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

































































theorem primrec_fin : Primrec fin := by
  unfold fin
  exact primrec₂_finAux.comp
    (Primrec.pair Primrec.id (Primrec.succ.comp Primrec.id))

end DomainTheory.DataTypesAsLattices
