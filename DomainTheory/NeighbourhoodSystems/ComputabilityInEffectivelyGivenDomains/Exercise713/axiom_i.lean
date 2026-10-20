module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)



/-- **Axiom (i).** `INCL` is reflexive. -/
theorem axiom_i (n : ℕ) : I.INCL n n := I.incl_refl n

end InclStructure
end DomainTheory.NeighbourhoodSystems.Exercise713
