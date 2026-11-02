module

public import DomainTheory.DataTypesAsLattices.Pomega.Pomega
import Mathlib.Tactic.Finiteness.Attr

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def ofNat (n : ℕ) : Pomega := {n}

end DomainTheory.DataTypesAsLattices
