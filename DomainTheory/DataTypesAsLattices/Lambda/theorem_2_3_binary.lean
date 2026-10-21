/-ai
Scott 1976, Theorem 2.3 (The reduction theorem), binary case. A binary map that is Scott continuous in each argument separately is represented by an element u of Pω: applying u first to x and then to y recovers the map.

The binary curry of the map is such an element, by the binary application law.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.curry2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.3 (The reduction theorem), binary case.** -/
theorem theorem_2_3_binary {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2_app f hfx hfy⟩

end DomainTheory.DataTypesAsLattices
