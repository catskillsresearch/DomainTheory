module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.toElementMap_evalBotMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v




section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)




theorem evalBotMap_comp_constFunMap : (evalBotMap A B).comp (constFunMap A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_evalBotMap, toApproxMap_constFunMap]

end FunSpace
end DomainTheory.NeighbourhoodSystems
