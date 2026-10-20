module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_split
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem pairTok_fstTok_sndTok (z : (prodTok D₀ D₁).Element) : pairTok (fstTok z) (sndTok z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prodTok_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prodTok_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
