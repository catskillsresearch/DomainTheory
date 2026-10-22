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


theorem proj₁_comp_embedSnd : (proj₁ A B).comp (embedSnd A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    simp [embedSnd, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₁, snd_pair]

end Prod
end DomainTheory.NeighbourhoodSystems
