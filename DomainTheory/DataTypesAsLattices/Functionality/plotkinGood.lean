/-ai
An element u is Plotkin-good for p, q, and j when, for some m, it equals the iterate Z m (e p) (e q), or that iterate with the singleton pair of j and m adjoined.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Z

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def plotkinGood (p q j : ℕ) (u : Pomega) : Prop :=
  ∃ m, u = Z m (e p) (e q) ∨
    u = Z m (e p) (e q) ∪ {pair j m}

end DomainTheory.DataTypesAsLattices
