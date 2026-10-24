module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branch
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_prefix_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Two neighbourhoods present in a common element of `|B|` have comparable generating prefixes
(their cones cannot be disjoint, since the intersection is a nonempty cone). -/
theorem prefix_comparable_of_mem {σ τ : Str} (y : B.Element)
    (hσ : y.mem (cone σ)) (hτ : y.mem (cone τ)) : σ <+: τ ∨ τ <+: σ := by
  have hi : y.mem (cone σ ∩ cone τ) := y.inter_mem hσ hτ
  obtain ⟨ρ, hρ⟩ := y.sub hi
  rcases cone_trichotomy σ τ with h | h | h
  · exact Or.inr (cone_subset_cone.mp h)
  · exact Or.inl (cone_subset_cone.mp h)
  · exfalso
    have hmem : ρ ∈ cone ρ := mem_cone.mpr List.prefix_rfl
    rw [← hρ, h] at hmem
    simp at hmem

end DomainTheory.NeighbourhoodSystems.Exercise113
