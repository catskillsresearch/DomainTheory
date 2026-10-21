/-ai
The composite of the second embedding after the second projection lies below the identity on the product.

On a pair, the composite returns the pair of bottom with the second component. That pair lies below the original pair because bottom lies below the first component and the second components agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


theorem embedSnd_comp_proj₁_le : (embedSnd A B).comp (proj₁ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₁, snd_pair, embedSnd,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨A.bot_le x, le_refl y⟩

end Prod
end DomainTheory.NeighbourhoodSystems
