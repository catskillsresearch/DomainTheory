/-ai
Doubling preserves the prefix order.

A prefix is a concatenation with some tail, and doubling grows under that concatenation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_append

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Prefix-monotonicity of `hOut`.** `σ <+: σ' → hOut σ <+: hOut σ'`. -/
theorem hOut_mono {σ σ' : Str} (h : σ <+: σ') : hOut σ <+: hOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact hOut_append σ t

end DomainTheory.NeighbourhoodSystems.Exercise218
