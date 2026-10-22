module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.constFunMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.evalBotMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

@[simp] theorem toApproxMap_constFunMap (b : B.Element) (a : A.Element) :
    (toApproxMap ((constFunMap A B).toElementMap b)).toElementMap a = b := by
  rw [constFunMap, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

end FunSpace

variable {α : Type u} (D : NeighborhoodSystem α)
end DomainTheory.NeighbourhoodSystems
