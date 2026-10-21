/-ai
If every component of Y belongs to MemA, then fromAA s contains the true-tagged tuple of Y if and only if s contains the right injection of the proper product of Y.

In the forward direction the membership clause is the set of all strings, a false-tagged tuple, or a true-tagged tuple. The first contradicts the tuple not being the whole set of strings. The false clause contradicts distinct tags giving distinct tuples, using a nonempty witness from memA_nonempty at index zero. The true clause uses injectivity of embTuple. The reverse direction is the true disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne_univ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.fromAA_mem_embF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

@[simp] theorem fromAA_mem_embT (hn : 0 < n) {s : (AAsys hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (fromAA hn s).mem (embTuple true Y) ↔ s.mem (inj₁ (prodN Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ Y)
    · exact absurd heq.symm
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩)))
    · rw [funext (embTuple_injective heq)]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
