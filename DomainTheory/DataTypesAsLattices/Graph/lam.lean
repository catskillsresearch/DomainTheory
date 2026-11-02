
module

public import DomainTheory.DataTypesAsLattices.Graph.graph
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lam (τ : Pomega → Pomega) : Pomega := graph τ

namespace lam

theorem eq_graph (τ : Pomega → Pomega) : lam τ = graph τ := rfl

end lam

end DomainTheory.DataTypesAsLattices
