/-ai
The first projection after the first embedding is the identity on A.

Both inequalities reduce to the same computation: the first component of the pair of an element with bottom is that element.
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


theorem proj₀_comp_embedFst : (proj₀ A B).comp (embedFst A B) = idMap A := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro a <;>
    simp [embedFst, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₀, fst_pair]

end Prod
end DomainTheory.NeighbourhoodSystems
