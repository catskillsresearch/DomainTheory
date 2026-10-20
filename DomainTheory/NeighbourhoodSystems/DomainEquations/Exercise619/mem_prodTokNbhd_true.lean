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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem mem_prodTokNbhd_true {X Y : Set Str} {w' : Str} :
    (true :: w') ∈ prodTokNbhd X Y ↔ w' ∈ Y := by
  simp only [prodTokNbhd, Set.mem_insert_iff, Set.mem_union, mem_embBit]
  constructor
  · rintro (h | ⟨u, hu, hX⟩ | ⟨u, hu, hY⟩)
    · exact absurd h (by simp)
    · rw [List.cons.injEq] at hu; exact absurd hu.1 (by decide)
    · rw [List.cons.injEq] at hu; rw [hu.2]; exact hY
  · intro h; exact Or.inr (Or.inr ⟨w', rfl, h⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
