module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

noncomputable def piDApply (d f : ApproximableMap U U) : ApproximableMap U U :=
  (evalMap U U).comp (paired (jArrow.comp (subU.comp (d.comp subU))) (f.comp subU))

noncomputable def piDUncurried (d : ApproximableMap U U) : ApproximableMap (prod (funSpace U U) U) U :=
  (evalMap U U).comp
    (paired
      (jArrow.comp (subU.comp (d.comp (subU.comp (proj₁ (funSpace U U) U)))))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) U) (subU.comp (proj₁ (funSpace U U) U)))))

noncomputable def piD (d : ApproximableMap U U) : ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (piDUncurried d)

noncomputable def piDTypeMap (d : ApproximableMap U U) : ApproximableMap U (funSpace U U) :=
  jArrow.comp (subU.comp d)

noncomputable def piDType (d : ApproximableMap U U) (s : U.Element) : ApproximableMap U U :=
  toApproxMap ((piDTypeMap d).toElementMap s)

end DomainTheory.NeighbourhoodSystems
