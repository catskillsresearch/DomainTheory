module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap_strict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_comm
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prodFunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.iterAlg

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The descent homomorphism `(𝒟^∞, i) → (E, k)`**: the strict map `descMap k` (existence half),
with the homomorphism square supplied by `descMap_comm`. -/
def descAlgHom (Dom : StrictDomainObj.{w}) (B : TAlgebra (prodFunctor Dom)) :
    AlgHom (iterAlg Dom) B where
  hom := ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩
  comm := by
    apply Subtype.ext
    show (descMap B.str.1).comp (imap Dom.sys)
       = B.str.1.comp (prodMap (idMap Dom.sys) (descMap B.str.1))
    exact descMap_comm B.str.1

end Exercise618

end DomainTheory.NeighbourhoodSystems
