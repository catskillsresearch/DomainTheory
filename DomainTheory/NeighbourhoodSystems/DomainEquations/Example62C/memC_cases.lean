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

/-- **Example 6.2 — the shape of a `C`-neighbourhood.** Every neighbourhood of `C` is the master
`Σ* = cone []`, the terminator `{Λ} = {[]}`, a `0`-copy `0X` with `X ∈ C`, or a `1`-copy `1X`. -/
theorem memC_cases {W : Set Str} (hW : C.mem W) :
    W = Set.univ ∨ W = ({[]} : Set Str)
      ∨ (∃ X, C.mem X ∧ W = embBit false X) ∨ (∃ Y, C.mem Y ∧ W = embBit true Y) := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl cone_nil
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨cone σ', memC_cone σ', (embBit_cone false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨cone σ', memC_cone σ', (embBit_cone true σ').symm⟩))
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨{σ'}, memC_singleton σ', (embBit_singleton false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨{σ'}, memC_singleton σ', (embBit_singleton true σ').symm⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
