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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem prodTok_mem_iff {W : Set Str} :
    (prodTok D₀ D₁).mem W ↔ ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y := Iff.rfl

end Exercise619

end DomainTheory.NeighbourhoodSystems
