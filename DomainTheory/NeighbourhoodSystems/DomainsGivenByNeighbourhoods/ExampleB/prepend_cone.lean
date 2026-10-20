module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.B_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.B_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_prepend

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element. -/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
