module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Tactic.Continuity.Init

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Directed union of `f` on finite subsets of `x`. -/
def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
