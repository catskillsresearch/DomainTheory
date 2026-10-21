/-ai
If Y is a neighbourhood of C, then fromCC s contains the 1-copy of Y if and only if s contains the second C-copy of Y.

In the forward direction the membership clause is the set of all strings, the singleton of the empty string, a 0-copy, or a 1-copy. The first contradicts a bit copy not being the whole set of strings. The singleton clause contradicts that singleton differing from a bit copy. The 0-copy clause contradicts distinct bits giving distinct copies, using that the underlying neighbourhood is nonempty. The 1-copy clause uses injectivity of embBit. The reverse direction is the 1-copy disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.singleton_nil_ne_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.CC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.fromCC_mem_embF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem fromCC_mem_embT {s : CC.Element} {Y : Set Str} (hY : C.mem Y) :
    (fromCC s).mem (embBit true Y) ↔ s.mem (j2 Y) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (singleton_nil_ne_embBit true Y)
    · exact absurd heqj.symm (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X' hX'))
    · rw [embBit_injective heqj]; exact hs
  · intro hs; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
