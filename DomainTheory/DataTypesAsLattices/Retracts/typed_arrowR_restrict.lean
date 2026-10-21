/-ai
If a set is typed by the function space of a retract a with a set b, then the set equals its composite with a.

The typing equation writes the set as the composite of b with the composite of the set and a. Composing that expression on the right with a does not change it, by comparing graphs and using idempotence of a. Substituting the rewritten form into the composite of the set with a and chaining these equalities gives the restriction equation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem typed_arrowR_restrict {a b u : Pomega}
    (ha : IsRetract a) (hu : typed u (arrowR a b)) :
    u = comp u a := by
  have hu' := typed_of_arrowR hu
  have h : comp (comp b (comp u a)) a = comp b (comp u a) := by
    apply graph_ext
    intro x
    simp only [comp_app]
    rw [retract_app ha]
  have : comp u a = comp (comp b (comp u a)) a := by
    conv_lhs => rw [hu']
  exact ((this.trans h).trans hu'.symm).symm

end DomainTheory.DataTypesAsLattices
