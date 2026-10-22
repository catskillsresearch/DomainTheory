module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.DomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.IsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Iso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63Inst2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u


variable {Obj : Type u} [Category Obj]


variable {T : Endofunctor Obj}


namespace AlgHom


@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = (𝟙 A.carrier) := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom


end DomainTheory.NeighbourhoodSystems
