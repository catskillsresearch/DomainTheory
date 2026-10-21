/-ai
For a neighbourhood Y of B, the image toBB x contains the right injection of Y if and only if x contains the 1-copy embBit true Y.

In the forward direction the membership clause is the master, a left injection, or a right injection. The master clause contradicts the basepoint not lying in a right injection. The left clause takes a nonempty witness in the left neighbourhood and produces a left-injection token, which cannot lie in a right injection. The right clause uses injectivity of the right injection. The reverse direction is the right disjunct of the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem toBB_mem_inj₁ {x : B.Element} {Y : Set Str} (hY : B.mem Y) :
    (toBB x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := B_nonempty X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
