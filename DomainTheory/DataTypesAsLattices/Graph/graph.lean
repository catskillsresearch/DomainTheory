
module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

def lam (τ : Pomega → Pomega) : Pomega := graph τ

namespace lam

theorem eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := rfl

end lam

end DomainTheory.DataTypesAsLattices
