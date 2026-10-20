module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone_subset_cone

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either one contains the
other, or they are disjoint (incomparable prefixes have no common extension). Choice-free: the
prefix relation on `List Bool` is decidable. -/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

end DomainTheory.NeighbourhoodSystems.ExampleB
