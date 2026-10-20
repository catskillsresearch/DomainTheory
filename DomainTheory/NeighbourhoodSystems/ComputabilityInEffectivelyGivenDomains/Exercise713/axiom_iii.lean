module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)



/-- **Axiom (iii).** There is an `INCL`-greatest code. -/
theorem axiom_iii : ∃ m, ∀ n, I.INCL n m := ⟨I.topIdx, I.topIdx_spec⟩

end InclStructure
end DomainTheory.NeighbourhoodSystems.Exercise713
