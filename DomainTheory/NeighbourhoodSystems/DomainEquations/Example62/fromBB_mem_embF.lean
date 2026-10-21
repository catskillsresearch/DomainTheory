/-ai
For a neighbourhood X of the binary-sequence domain, the element rebuilt from a sum element contains the false-bit tagging of X if and only if the sum element contains the left injection of X.

If the rebuilt element contains that tagging, the witnessing clause is not the master, because a bit tagging is distinct from the full set of strings, and it is not a true-bit tagging, because the booleans differ and X is nonempty. The remaining clause is a false-bit tagging of some neighbourhood, and injectivity makes that neighbourhood equal to X. Conversely, the false-bit clause of the rebuilt membership records that the left injection of X belongs to the sum element.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem fromBB_mem_embF {s : BB.Element} {X : Set Str} (hX : B.mem X) :
    (fromBB s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
