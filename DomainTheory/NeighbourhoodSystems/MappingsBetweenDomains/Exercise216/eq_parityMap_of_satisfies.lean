/-ai
An approximable map from the binary-string domain into the truth-value domain that satisfies the three parity equations equals the parity map.

Extensionality reduces the equality to agreement of relations. If the input neighbourhood is a cone, the relation of the given map is membership in the element map at the corresponding principal element; rewriting the principal element as a prefixed bottom element, the recursive core replaces that element map by the scan of the string, and the parity map relates the cone by that same scan. If the input is not a neighbourhood, each relation would require it to be a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.key

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Exercise 2.16, second half.** `parityMap` is the *unique* approximable map `B → T`
satisfying `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = parityMap` to matching relations on cones,
which is exactly `key` read through `rel_iff_mem_principal`/`parityMap_rel_cone`. -/
theorem eq_parityMap_of_satisfies {g : ApproximableMap B Example23.T}
    (hg : SatisfiesParityEquations g) : g = Example23.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Example23.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Example23.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Example23.parityMap.rel_dom hr) hX⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
