/-ai
The composition of the function space from a to b after the function space from a' to b' equals the function space from a' after a to b after b'. This is the composite form of Scott's equation (4.11).

Graph extensionality reduces the equality to values. The application law writes the left-hand value as a nested composition, the inner application is rewritten by the same law, and a second graph extensionality matches the two associations by the application law for composition.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (4.11).** Composition of function-space retracts. -/
theorem eq_4_11_comp (a b a' b' : Pomega) :
    comp (arrowR a b) (arrowR a' b') = arrowR (comp a' a) (comp b b') := by
  apply graph_ext
  intro u
  calc
    funOf (arrowR a b) (funOf (arrowR a' b') u)
        = comp b (comp (funOf (arrowR a' b') u) a) := arrowR_app _ _ _
    _ = comp b (comp (comp b' (comp u a')) a) := by rw [arrowR_app]
    _ = comp (comp b b') (comp u (comp a' a)) := by
      apply graph_ext
      intro x
      simp only [comp_app]

end DomainTheory.DataTypesAsLattices
