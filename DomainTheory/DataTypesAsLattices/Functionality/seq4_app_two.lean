/-ai
The four-way sequence of a, b, c, and d sends the numeral 2 to c.

Rewrite by the application law, by the successor law for the conditional, by the successor law for the predecessor, by the law for the conditional at the numeral 1, by the successor law for the predecessor again, and by the law for the conditional at the numeral 0.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_zero
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_succ
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_app_two (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 2) = c := by
  rw [seq4_app, condSet_ofNat_succ, predSet_ofNat_succ, condSet_ofNat_one,
    predSet_ofNat_succ, condSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
