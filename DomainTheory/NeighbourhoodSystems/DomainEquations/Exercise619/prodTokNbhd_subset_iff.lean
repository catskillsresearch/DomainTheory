/-ai
One product neighbourhood is contained in another if and only if each component is contained in the corresponding component.

From an inclusion, a member of the first component is a false-tagged word of the smaller neighbourhood, hence of the larger, and the membership criterion returns it to the first component; the true tag does the same for the second component. Conversely, the empty word lies in every product neighbourhood, a false-tagged word is carried by the first inclusion, and a true-tagged word is carried by the second.
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (1) for the product: inclusion of product neighbourhoods is componentwise. -/
theorem prodTokNbhd_subset_iff {X X' Y Y' : Set Str} :
    prodTokNbhd X Y ⊆ prodTokNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · exact mem_prodTokNbhd_false.mp (h (mem_prodTokNbhd_false.mpr ha))
    · exact mem_prodTokNbhd_true.mp (h (mem_prodTokNbhd_true.mpr hb))
  · rintro ⟨hX, hY⟩ w hw
    cases w with
    | nil => exact mem_prodTokNbhd_nil
    | cons b w' =>
      cases b with
      | false => exact mem_prodTokNbhd_false.mpr (hX (mem_prodTokNbhd_false.mp hw))
      | true => exact mem_prodTokNbhd_true.mpr (hY (mem_prodTokNbhd_true.mp hw))

end Exercise619

end DomainTheory.NeighbourhoodSystems
