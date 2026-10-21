/-ai
If the right injection of a set Y of strings is a neighbourhood of the sum BB, then Y is a neighbourhood of B.

The membership splits into the sum master, a left summand, or a right summand. The master case is impossible because the basepoint belongs to the master and not to a right injection. The left-summand case takes a nonempty witness in B and produces a left-injection token, which cannot lie in a right injection. The right-summand case uses injectivity of the right injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_inj₁_inv {Y : Set Str} (h : BB.mem (inj₁ Y)) : B.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := B_nonempty X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Example62

end DomainTheory.NeighbourhoodSystems
