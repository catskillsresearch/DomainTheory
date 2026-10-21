/-ai
The image of the colimit under T equals the colimit as domain objects.

Extensionality of domain objects applies to the carrier identification and to the equality of the transported system with the colimit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colimCeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_eq_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.domainObj_ext

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- **`T(𝒟) ≅ 𝒟` is the identity**, packaged as a `DomainObj` equality `T(𝒟) = 𝒟`. -/
theorem colimObj_eq (s : Setup.{w}) :
    s.T.obj ⟨s.Tok, colim s⟩ = (⟨s.Tok, colim s⟩ : DomainObj) :=
  domainObj_ext (s.T.obj ⟨s.Tok, colim s⟩).sys (colimCeq s) (Tcolim_eq_colim s)

end Theorem614

end DomainTheory.NeighbourhoodSystems
