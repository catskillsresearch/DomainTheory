module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_3

@[expose] public section

section
universe u
namespace DomainTheory.NeighbourhoodSystems
variable {Obj : Type u} [Category Obj]

structure TAlgebra (T : Endofunctor Obj) where

  carrier : Obj

  str : ((T.obj carrier) ⟶ carrier)

end DomainTheory.NeighbourhoodSystems
end

section

universe u

namespace DomainTheory.NeighbourhoodSystems

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

structure AlgHom (A B : TAlgebra T) where

  hom : (A.carrier ⟶ B.carrier)

  comm : hom ⊚ A.str = B.str ⊚ T.map hom

end DomainTheory.NeighbourhoodSystems
end
