/-ai
Abstraction of a map tau, in the sense of Table 2, is the graph of tau.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Abstraction: `λ x. τ` as a graph (Table 2). -/
def lam (τ : Pomega → Pomega) : Pomega := graph τ

end DomainTheory.DataTypesAsLattices
