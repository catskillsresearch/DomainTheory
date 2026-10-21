/-ai
The inverse limit of an endomap F consists of the sequences in which every coordinate is typed by the corresponding iterate of F from the empty set, and each coordinate equals the application of that iterate to the next coordinate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- The inverse limit of the ranges of `Fⁿ(⊥)`: points are typed at every
stage and adjacent coordinates satisfy Scott's projection equation. -/
def RetractInverseLimit (F : Pomega → Pomega) :=
  {v : ℕ → Pomega //
    (∀ n, typed (v n) (iterateBot F n)) ∧
      ∀ n, v n = funOf (iterateBot F n) (v (n + 1))}

end DomainTheory.DataTypesAsLattices
