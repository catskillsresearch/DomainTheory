/-ai
If one string is a prefix of another, the output of the shorter string is a prefix of the output of the longer string.

Write the longer string as the shorter one followed by a tail, and apply growth of the output under extension.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.del_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_true
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Prefix-monotonicity of the output.** Extending the input prefix can only extend the guaranteed
output: `σ <+: σ' → out σ <+: out σ'`. This is the heart of Definition 2.1(iii) for `g`. -/
theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t

end DomainTheory.NeighbourhoodSystems.Example24
