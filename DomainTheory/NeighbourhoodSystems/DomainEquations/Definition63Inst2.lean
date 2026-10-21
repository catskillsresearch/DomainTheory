/-ai
Domains and approximable maps form a category. A morphism is an approximable map between the underlying neighbourhood systems, the identity morphism is the identity approximable map, and the composite of two morphisms is the project's composite in the order of the first morphism followed by the second. The two identity laws are the identity laws for approximable maps, and associativity is the associativity law for approximable maps read in that order.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Category
public import DomainTheory.NeighbourhoodSystems.DomainEquations.DomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.TAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.AlgHom
public import DomainTheory.NeighbourhoodSystems.DomainEquations.IsInitial
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Iso

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

universe u v w

/-- **The category of domains and approximable maps** (Scott's prose preceding Definition 6.3):
identities and associative composition come from Theorem 2.5 (`idMap_comp`, `comp_idMap`,
`comp_assoc`). -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := ApproximableMap.idMap D.sys
  comp f g := g.comp f
  id_comp f := ApproximableMap.comp_idMap f
  comp_id f := ApproximableMap.idMap_comp f
  assoc f g h := (ApproximableMap.comp_assoc h g f).symm

end DomainTheory.NeighbourhoodSystems
