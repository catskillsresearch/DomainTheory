module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.embedIntoPow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.component_embedIntoPow_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.component_embedIntoPow_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **`embedIntoPow ∘ head ≤ id`**: re-stacking after reading only the head can only forget
information (all coordinates past the head collapse to `⊥`). -/
theorem embedIntoPow_comp_head_le : (embedIntoPow V).comp (head V) ≤ idMap (iterSys V) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_comp, toElementMap_idMap]
  apply le_of_component_le
  intro n
  cases n with
  | zero => rw [component_embedIntoPow_zero, head_apply]
  | succ m => rw [component_embedIntoPow_succ]; exact NeighborhoodSystem.bot_le V _

end DomainTheory.NeighbourhoodSystems
