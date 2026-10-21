/-ai
If one element of the binary neighbourhood system contains both the cone of a string σ and the cone of a string τ, then σ is a prefix of τ or τ is a prefix of σ.

The intersection of the two cones belongs to the element, so some cone is contained in that intersection. Trichotomy of cones gives an inclusion one way or the other, and each inclusion is a prefix, or else the cones are disjoint. In the disjoint case the generating string of the contained cone belongs to its own cone, and rewriting that membership through the containment puts it in the empty set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.Basic

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
