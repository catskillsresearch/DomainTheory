/-ai
A right-copy neighbourhood of the sum arises only from the product factor, so the copied set is a neighbourhood of the product of the two sharp systems.

It is not the master, because the master token does not lie in a right copy. It is not a left copy, because a token of the nonempty neighbourhood of D lies in the left copy and not in the right. The remaining case is a right copy, and injectivity of the right embedding returns the product membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- A sum-neighbourhood of the form `1V` arises only from the right factor, so `V ∈ 𝒟^§ × 𝒟^§`. -/
theorem sum_mem_inj₁_inv {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    (h : (sumSys D hD).mem (inj₁ V)) : (prod (Dsharp D hD) (Dsharp D hD)).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := hD X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
