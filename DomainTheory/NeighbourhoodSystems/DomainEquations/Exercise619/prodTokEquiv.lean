/-ai
prodTokEquiv is the order isomorphism between elements of the concrete token product and pairs of elements of the two factors, the token-level form of Scott's Proposition 3.2. It sends an element to the pair of its components, and the inverse pairs the two components. The two directions are inverse by the pairing-of-components theorem and by simplification. The map preserves and reflects order because a neighbourhood of the smaller element splits into the two slices, which the component inequalities carry to the larger element, while each component inequality is the corresponding slice of a product inequality.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_split
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.pairTok_fstTok_sndTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fstTok_pairTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sndTok_pairTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The order-isomorphism `|D₀ × D₁|ₜₒₖ ≃o |D₀| × |D₁|` (Scott's Proposition 3.2, token-level). -/
def prodTokEquiv : (prodTok D₀ D₁).Element ≃o D₀.Element × D₁.Element where
  toFun z := (fstTok z, sndTok z)
  invFun p := pairTok p.1 p.2
  left_inv z := pairTok_fstTok_sndTok z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prodTok_mem_split hX hY).mp hW
      have hX' : (fstTok z').mem X := h1 X ⟨hX, ha⟩
      have hY' : (sndTok z').mem Y := h2 Y ⟨hY, hb⟩
      exact (prodTok_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
