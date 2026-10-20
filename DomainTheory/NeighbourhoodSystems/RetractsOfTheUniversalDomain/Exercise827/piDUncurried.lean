module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`Π(d)(x)(t)`, uncurried**: an `ApproximableMap ((𝒰→𝒰) × 𝒰) 𝒰`, jointly continuous in
`(x, t)` for `d` fixed. -/
noncomputable def piDUncurried (d : ApproximableMap U U) : ApproximableMap (prod (funSpace U U) U) U :=
  (evalMap U U).comp
    (paired
      (jArrow.comp (subU.comp (d.comp (subU.comp (proj₁ (funSpace U U) U)))))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) U) (subU.comp (proj₁ (funSpace U U) U)))))

end DomainTheory.NeighbourhoodSystems
