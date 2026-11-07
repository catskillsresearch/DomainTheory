module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Cond

theorem U_mem_nonempty : ∀ X, U.mem X → X.Nonempty := fun _ hX => hX.2.1

theorem funSpaceUU_isEffectivelyGiven : (funSpace U U).IsEffectivelyGiven :=
  funSpace_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

noncomputable def funSpaceUUPresentation : ComputablePresentation (funSpace U U) :=
  funSpaceUU_isEffectivelyGiven.some

noncomputable def lamComb (a b : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a)))

theorem prodUU_isEffectivelyGiven : (prod U U).IsEffectivelyGiven :=
  prod_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

noncomputable def prodUUPresentation : ComputablePresentation (prod U U) :=
  prodUU_isEffectivelyGiven.some

theorem sumUU_isEffectivelyGiven :
    (sum U U U_mem_nonempty U_mem_nonempty).IsEffectivelyGiven :=
  sum_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

noncomputable def sumUUPresentation : ComputablePresentation (sum U U U_mem_nonempty U_mem_nonempty) :=
  sumUU_isEffectivelyGiven.some

end DomainTheory.NeighbourhoodSystems
