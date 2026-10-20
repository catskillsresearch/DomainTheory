module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.DomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.IsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Iso
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63Inst2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u v w

variable {Obj : Type u} [Category Obj]

variable {T : Endofunctor Obj}

namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := (𝟙 A.carrier)
  comm := by
    simp only [compAfter]
    rw [CategoryTheory.Category.comp_id, T.map_id, CategoryTheory.Category.id_comp]

end AlgHom

end DomainTheory.NeighbourhoodSystems
