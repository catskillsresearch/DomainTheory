module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems

/-- An **overlap** of period `p ≥ 1` at offset `i`: a factor of length `2p+1` with period `p`. -/
def Overlap (i p : ℕ) : Prop := 1 ≤ p ∧ ∀ k, k ≤ p → tm (i + k) = tm (i + p + k)

end DomainTheory.NeighbourhoodSystems.Exercise516
