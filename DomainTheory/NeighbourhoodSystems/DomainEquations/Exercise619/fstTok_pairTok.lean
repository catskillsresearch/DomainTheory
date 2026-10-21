/-ai
The first component of the pairing of two elements is the first element.

Two elements agree when they contain the same neighbourhoods. A neighbourhood of that first component is, by the membership criterion for pairs, a neighbourhood of the first element. Conversely, a neighbourhood of the first element is a neighbourhood of the first factor, and the pair contains the product neighbourhood of that set with the master of the second element.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_pairTok_prodTokNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fstTok_pairTok (x : D₀.Element) (y : D₁.Element) : fstTok (pairTok x y) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).1
  · intro hX; exact ⟨x.sub hX, mem_pairTok_prodTokNbhd.mpr ⟨hX, y.master_mem⟩⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
