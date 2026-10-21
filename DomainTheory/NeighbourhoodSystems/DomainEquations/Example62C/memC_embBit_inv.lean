/-ai
If the bit embedding of W is a neighbourhood of C, then W is a neighbourhood of C.

Membership splits into a cone and a singleton. In the cone case the selector lies in its own cone and hence in the embedded set, so it is the bit followed by a word; rewriting by the cone form of embedding and applying injectivity of embedding shows that W is the cone of that word, which is a neighbourhood. In the singleton case the selector lies in its own singleton and the same extraction, rewritten by the singleton form of embedding, shows that W is the singleton of the remaining word, which is a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.embBit_singleton

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

/-- If `bW ∈ C` then `W ∈ C`. -/
theorem memC_embBit_inv {b : Bool} {W : Set Str} (h : C.mem (embBit b W)) : C.mem W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_cone] at hσ; rw [embBit_injective hσ]; exact memC_cone w'
  · have hmem : σ ∈ embBit b W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set Str))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_singleton] at hσ; rw [embBit_injective hσ]; exact memC_singleton w'

end Example62C

end DomainTheory.NeighbourhoodSystems
