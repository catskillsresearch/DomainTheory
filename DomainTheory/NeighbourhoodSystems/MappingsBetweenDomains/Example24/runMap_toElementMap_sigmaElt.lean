/-ai
A set belongs to the run map at the element obtained by prepending a string exactly when the set is a neighbourhood and some cone of the element has the cone of the output of the concatenation contained in the set.

From a membership witness, the inner neighbourhood is a cone and the cone inclusion is a prefix of the concatenation, so prefix-monotonicity of the output composes with the output inclusion. Conversely the cone of the concatenation belongs to the shifted element by the prepend inclusion, and the relation on that cone is the stated condition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap_rel_cone

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB










/-- **The "shift formula" for `runMap` (input side).** Reading off `g(σx)` depends on `x` only
through *some* cone `cone τ ∈ x`, via the output of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`out_mono`), so the longest one —
`σ ++ τ` itself — already witnesses the answer. -/
theorem runMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out (σ ++ τ)) ⊆ Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hYmem, hsubOut⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, hYmem, (cone_subset_cone.mpr (out_mono (cone_subset_cone.mp hsub))).trans hsubOut⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩,
      (runMap_rel_cone (σ ++ τ) Y).mpr ⟨hYmem, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Example24
