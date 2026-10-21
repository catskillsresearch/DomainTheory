/-ai
Scott 1976, Theorem 2.3, ternary case. A ternary map that is Scott continuous in each argument separately is represented by an element u of Pω under three iterated applications.

The ternary curry of the map is such an element, by the ternary application law.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.curry3_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.3, ternary case** (the usual reduction of `k`). -/
theorem theorem_2_3_ternary {f : Pomega → Pomega → Pomega → Pomega}
    (hf0 : ∀ y z, IsScottContinuous (fun x => f x y z))
    (hf1 : ∀ x z, IsScottContinuous (fun y => f x y z))
    (hf2 : ∀ x y, IsScottContinuous (fun z => f x y z)) :
    ∃ u, ∀ x y z, funOf (funOf (funOf u x) y) z = f x y z :=
  ⟨curry3 f hf0 hf1 hf2, curry3_app f hf0 hf1 hf2⟩

end DomainTheory.DataTypesAsLattices
