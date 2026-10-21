/-ai
Equal product neighbourhoods have equal components.

Equality gives both inclusions. Each inclusion is componentwise by the subset criterion, and the two inclusions in each component give equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_subset_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem prodTokNbhd_injective {X X' Y Y' : Set Str} (h : prodTokNbhd X Y = prodTokNbhd X' Y') :
    X = X' ∧ Y = Y' :=
  ⟨Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).1
      (prodTokNbhd_subset_iff.mp h.symm.subset).1,
   Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).2
      (prodTokNbhd_subset_iff.mp h.symm.subset).2⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
