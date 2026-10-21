/-ai
The pinning of copy n to a set X is the set of index-token pairs whose token lies in X when the index equals n, and in the master neighbourhood otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- The `𝒟^∞`-neighbourhood pinning copy `n` to `X` and leaving all other copies at `Δ`: Scott's
`Δ^∞ ∩ (1ⁿ0X)`, i.e. the combination with `Xₙ = X` and `Xₘ = Δ` for `m ≠ n`. -/
def single (n : ℕ) (X : Set α) : Set (ℕ × α) :=
  {p | if p.1 = n then p.2 ∈ X else p.2 ∈ V.master}

end DomainTheory.NeighbourhoodSystems
