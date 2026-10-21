/-ai
If the left injection of a set X of strings is a neighbourhood of the sum BB, then X is a neighbourhood of B.

The membership splits into the sum master, a left summand, or a right summand. The master case is impossible because the basepoint belongs to the master and not to a left injection. The left-summand case uses injectivity of the left injection. The right-summand case takes a nonempty witness in B and produces a right-injection token, which cannot lie in a left injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_inj₀_inv {X : Set Str} (h : BB.mem (inj₀ X)) : B.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := B_nonempty Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Example62

end DomainTheory.NeighbourhoodSystems
