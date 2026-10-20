module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.no_overlap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems






/-- **The Thue–Morse sequence is cube-free.** A cube of period `p ≥ 1` (the factor `a·a·a` with
`|a| = p`) is in particular an overlap, so none exists. -/
theorem no_cube (i p : ℕ) (hp : 1 ≤ p) :
    ¬ ∀ k, k < 2 * p → tm (i + k) = tm (i + p + k) := by
  intro hcube
  exact no_overlap p i ⟨hp, fun k hk => hcube k (by omega)⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
