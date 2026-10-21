/-ai
If X is a neighbourhood of C, then the image of an element x of C contains the tagged middle copy of X if and only if x contains the false embedding of X.

In the forward direction the four forms of membership in the image are examined. The master would place the basepoint in the middle copy. The unit form would place a middle tag of a point of the nonempty set X in the left copy. A middle copy equals the given copy by injectivity and yields the membership. A right copy would place that middle tag in the right copy. Each mismatched token is excluded by the corresponding non-membership lemma. In the reverse direction the false-embedding form of the image is taken.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.toCC_mem_j0

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

@[simp] theorem toCC_mem_j1 {x : C.Element} {X : Set Str} (hX : C.mem X) :
    (toCC x).mem (j1 X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heq ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j0
    · rw [j1_injective heqj]; exact hz
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heqj ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · intro hz; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hz⟩))

end Example62C

end DomainTheory.NeighbourhoodSystems
