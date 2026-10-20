module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodMapHom

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The product endofunctor `T(X) = 𝒟 × X`** on `∅`-free domains and strict maps, for a fixed
domain `𝒟`. On objects `T(X) = 𝒟 × X`; on maps `T(f) = id_𝒟 × f`. -/
def prodFunctor (Dom : StrictDomainObj.{w}) : Endofunctor StrictDomainObj.{w} where
  obj := prodObj Dom
  map := prodMapHom Dom
  map_id X := Subtype.ext (by
    show prodMap (idMap Dom.sys) (idMap X.sys) = idMap (prod Dom.sys X.sys)
    exact prodMap_id)
  map_comp {X Y Z} g f := Subtype.ext (by
    show prodMap (idMap Dom.sys) (g.1.comp f.1)
       = (prodMap (idMap Dom.sys) g.1).comp (prodMap (idMap Dom.sys) f.1)
    have h := prodMap_comp (idMap Dom.sys) (idMap Dom.sys) g.1 f.1
    rw [idMap_comp] at h
    exact h)

end Exercise618

end DomainTheory.NeighbourhoodSystems
