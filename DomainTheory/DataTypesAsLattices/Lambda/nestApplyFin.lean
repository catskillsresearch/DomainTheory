module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def nestApplyFin (u : Pomega) : ∀ {n : ℕ}, (Fin n → Pomega) → Pomega
  | 0, _ => u
  | _n + 1, xs => nestApplyFin (funOf u (xs 0)) (Fin.tail xs)

end DomainTheory.DataTypesAsLattices
