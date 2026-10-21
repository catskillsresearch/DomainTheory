/-ai
The nested-graph representative of an n-ary map evaluates the map on the empty tuple when there are no arguments, and otherwise is the graph of the map obtained by consing one argument and taking the representative of what remains.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Nested-graph representative of an n-ary continuous map. -/
def curryFin : ∀ {n : ℕ}, ((Fin n → Pomega) → Pomega) → Pomega
  | 0, f => f Fin.elim0
  | _n + 1, f => graph (fun x => curryFin (fun xs => f (Fin.cons x xs)))

end DomainTheory.DataTypesAsLattices
