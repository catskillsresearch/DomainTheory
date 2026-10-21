/-ai
The run map is the only approximable self-map of the binary system that satisfies the four run equations.

Extensionality reduces equality to agreement of relations. When the domain set is a neighbourhood it is a cone, the relation of the given map on that cone is membership in the image of the principal element, the recursive core rewrites that image as the principal element of the output string, and the run map's relation on the cone is membership in the same principal filter. When the domain set is not a neighbourhood, each relation would require a domain neighbourhood, so both sides fail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap_rel_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.key

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB












/-- **Exercise 2.17, second half.** `runMap` is the *unique* approximable map `B → B` satisfying
`g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x`, `g(1) = ⊥`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = runMap` to matching relations on cones, which
is exactly `key` read through `rel_iff_mem_principal`/`runMap_rel_cone`. -/
theorem eq_runMap_of_satisfies {g : ApproximableMap B B} (hg : SatisfiesRunEquations g) :
    g = runMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ runMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, sigmaElt_bot, runMap_rel_cone]
    show (B.principal (memB_cone (out σ))).mem Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y
    exact B.mem_principal (memB_cone (out σ))
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX, fun hr => absurd (runMap.rel_dom hr) hX⟩

end DomainTheory.NeighbourhoodSystems.Example24
