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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_pairTok_prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok_pairTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem sndTok_pairTok (x : D₀.Element) (y : D₁.Element) : sndTok (pairTok x y) = y := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).2
  · intro hY; exact ⟨y.sub hY, mem_pairTok_prodTokNbhd.mpr ⟨x.master_mem, hY⟩⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
