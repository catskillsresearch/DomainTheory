/-ai
The morphism action of the product endofunctor sends a strict map f to the product of the identity on the fixed domain with f. That product is strict because both the identity and f are strict.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_prodMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodObj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The morphism action `T(f) = id_𝒟 × f`, strict by `isStrict_prodMap`. -/
def prodMapHom (Dom : StrictDomainObj.{w}) {X Y : StrictDomainObj.{w}} (f : (X ⟶ Y)) :
    ((prodObj Dom X) ⟶ (prodObj Dom Y)) :=
  ⟨prodMap (idMap Dom.sys) f.1, isStrict_prodMap isStrict_idMap f.2⟩

end Exercise618

end DomainTheory.NeighbourhoodSystems
