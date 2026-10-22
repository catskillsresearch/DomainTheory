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
