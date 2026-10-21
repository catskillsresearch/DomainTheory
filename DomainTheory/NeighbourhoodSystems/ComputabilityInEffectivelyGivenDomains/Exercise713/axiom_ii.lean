/-ai
The inclusion relation of an inclusion structure is transitive.

This is the transitivity datum of the structure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)


/-- **Axiom (ii).** `INCL` is transitive. -/
theorem axiom_ii {n m k : ℕ} (h1 : I.INCL n m) (h2 : I.INCL m k) : I.INCL n k := I.incl_trans h1 h2

end InclStructure
end DomainTheory.NeighbourhoodSystems.Exercise713
