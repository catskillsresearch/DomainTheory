module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.endofunctor

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

structure TAlgebra (T : Endofunctor Obj) where
  carrier : Obj
  str : ((T.obj carrier) ⟶ carrier)

structure AlgHom (A B : TAlgebra T) where
  hom : (A.carrier ⟶ B.carrier)
  comm : hom ⊚ A.str = B.str ⊚ T.map hom

end DomainTheory.NeighbourhoodSystems
