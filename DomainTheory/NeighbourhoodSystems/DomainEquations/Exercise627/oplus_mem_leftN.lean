/-ai
The left copy of a neighbourhood X of D₀ is a neighbourhood of the coalesced sum. The argument splits on whether X equals the master.

If X is the master, the left copy is the sum master, which is a neighbourhood. If X is distinct from the master, the left copy is the false tag of X, which is a proper left neighbourhood of the coalesced sum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_proper

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **only** classical step in Exercise 6.27: `leftN X` is an `𝒟 ⊕ ℰ`-neighbourhood. The proof
splits on the (undecidable for arbitrary `X`) test `X = Δ₀`. -/
theorem oplus_mem_leftN {X : Set Str} (hX : D₀.mem X) :
    (oplusTok D₀ D₁ h₀ h₁).mem (leftN D₀ D₁ X) := by
  by_cases h : X = D₀.master
  · rw [h, leftN_master]; exact (oplusTok D₀ D₁ h₀ h₁).master_mem
  · rw [leftN_proper h]; exact oplusTok_mem_embF hX h

end Exercise627

end DomainTheory.NeighbourhoodSystems
