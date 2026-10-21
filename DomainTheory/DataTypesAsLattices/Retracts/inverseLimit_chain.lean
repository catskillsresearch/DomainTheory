/-ai
The coordinates of a coherent inverse-limit sequence for a Scott-continuous map form a chain: an earlier coordinate is contained in a later one.

This is the chain monotonicity lemma applied to the successive inclusions of the coordinates.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem inverseLimit_chain {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n m, n ≤ m → v.1 n ⊆ v.1 m :=
  chain_mono v.1 (inverseLimit_mono hf v)

end DomainTheory.DataTypesAsLattices
