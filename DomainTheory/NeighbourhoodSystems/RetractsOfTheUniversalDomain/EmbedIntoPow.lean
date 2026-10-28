module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_11
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_17
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)

def embedIntoPow : ApproximableMap V (iterSys V) :=
  (push V).comp (paired (idMap V) (constMap V (iterSys V).bot))

theorem toElementMap_embedIntoPow (x : V.Element) :
    (embedIntoPow V).toElementMap x = (push V).toElementMap (pair x (iterSys V).bot) := by
  rw [embedIntoPow, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

theorem component_embedIntoPow_succ (x : V.Element) (n : ℕ) :
    component ((embedIntoPow V).toElementMap x) (n + 1) = V.bot := by
  rw [toElementMap_embedIntoPow, ← component_tail, tail_push, Exercise618.component_bot]

theorem component_embedIntoPow_zero (x : V.Element) :
    component ((embedIntoPow V).toElementMap x) 0 = x := by
  rw [toElementMap_embedIntoPow, ← head_apply, head_push]

theorem embedIntoPow_comp_head_le : (embedIntoPow V).comp (head V) ≤ idMap (iterSys V) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_comp, toElementMap_idMap]
  apply le_of_component_le
  intro n
  cases n with
  | zero => rw [component_embedIntoPow_zero, head_apply]
  | succ m => rw [component_embedIntoPow_succ]; exact NeighborhoodSystem.bot_le V _

theorem head_comp_embedIntoPow : (head V).comp (embedIntoPow V) = idMap V :=
  ApproximableMap.ext_of_toElementMap fun x => by
    rw [toElementMap_comp, toElementMap_idMap, head_apply, component_embedIntoPow_zero]

end DomainTheory.NeighbourhoodSystems
