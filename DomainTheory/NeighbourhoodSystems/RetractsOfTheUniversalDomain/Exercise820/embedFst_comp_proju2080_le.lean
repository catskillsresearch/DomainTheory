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


theorem embedFst_comp_proj₀_le : (embedFst A B).comp (proj₀ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₀, fst_pair, embedFst,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨le_refl x, B.bot_le y⟩

end Prod
end DomainTheory.NeighbourhoodSystems
