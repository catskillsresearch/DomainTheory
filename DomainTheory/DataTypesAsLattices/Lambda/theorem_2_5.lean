/-ai
Scott 1976, Theorem 2.5 (The first recursion theorem). If f is Scott continuous, then applying the Y combinator to the graph of f equals the least fixed point of f.

Rewrite by the application law for Y, then apply the first recursion theorem for the omega combinator.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_app
public import DomainTheory.DataTypesAsLattices.Lambda.omega_first_recursion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 2.5 (The first recursion theorem).**
If `u` is the graph of a continuous `f`, then `Y(u) = fix(f)`. -/
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  rw [Ycomb_app]
  exact omega_first_recursion hf

end DomainTheory.DataTypesAsLattices
