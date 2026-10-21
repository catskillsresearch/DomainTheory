/-ai
Scott 1976, (2.26): the abstraction over ω of a sequence of sets is the dollar combinator applied to the graph of the union of those values of the sequence whose indices lie in the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.26).** `λn∈ω. τ` is `$` applied to a graph. -/
def lamOmega (τ : ℕ → Pomega) : Pomega :=
  funOf dollarC (graph (fun z => ⋃ n ∈ z, τ n))

end DomainTheory.DataTypesAsLattices
