/-ai
For a neighbourhood X of B, the image toBB x contains the left injection of X if and only if x contains the 0-copy embBit false X.

In the forward direction the membership clause is the master, a left injection, or a right injection. The master clause contradicts the basepoint not lying in a left injection. The left clause uses injectivity of the left injection. The right clause takes a nonempty witness in X and produces a left-injection token, which cannot lie in a right injection. The reverse direction is the left disjunct of the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

@[simp] theorem toBB_mem_inj₀ {x : B.Element} {X : Set Str} (hX : B.mem X) :
    (toBB x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := B_nonempty X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
