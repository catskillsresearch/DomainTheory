module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem typed_arrowR_restrict {a b u : Pomega}
    (ha : Retract a) (hu : typed u (arrowR a b)) :
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
