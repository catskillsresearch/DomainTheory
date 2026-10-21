/-ai
Iterated application of a nested-graph representative returns the element on the empty tuple, and on a nonempty tuple applies the element to the head and recurses on the tail.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Iterated application of a nested-graph representative. -/
def nestApplyFin (u : Pomega) : ∀ {n : ℕ}, (Fin n → Pomega) → Pomega
  | 0, _ => u
  | _n + 1, xs => nestApplyFin (funOf u (xs 0)) (Fin.tail xs)

end DomainTheory.DataTypesAsLattices
