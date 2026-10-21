/-ai
For a neighbourhood Y of the binary-sequence domain, the element rebuilt from a sum element contains the true-bit tagging of Y if and only if the sum element contains the right injection of Y.

If the rebuilt element contains that tagging, the witnessing clause is not the master, because a bit tagging is distinct from the full set of strings, and it is not a false-bit tagging, because the booleans differ and the false-tagged neighbourhood is nonempty. The remaining clause is a true-bit tagging of some neighbourhood, and injectivity makes that neighbourhood equal to Y. Conversely, the true-bit clause of the rebuilt membership records that the right injection of Y belongs to the sum element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem fromBB_mem_embT {s : BB.Element} {Y : Set Str} (hY : B.mem Y) :
    (fromBB s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
