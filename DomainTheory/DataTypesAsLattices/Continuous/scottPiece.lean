module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Tactic.Continuity.Init

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
