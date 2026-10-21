/-ai
The four-way sequence of a, b, c, and d sends the numeral 3 to d.

Rewrite by the application law, then by the successor law for the conditional, the successor law for the predecessor, the successor law for the conditional again, the successor law for the predecessor again, the law for the conditional at the numeral 1, the lemma that the predecessor iterated on its own numeral is the numeral 0, and the law for the conditional at the numeral 0.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_zero
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_succ
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq4_app_three (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 3) = d := by
  rw [seq4_app, condSet_ofNat_succ, predSet_ofNat_succ, condSet_ofNat_succ,
    predSet_ofNat_succ, condSet_ofNat_one, predSet_iterate_self,
    condSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
