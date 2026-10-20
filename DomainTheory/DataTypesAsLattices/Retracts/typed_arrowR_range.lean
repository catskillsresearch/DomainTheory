module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices









































theorem typed_arrowR_range {a b u : Pomega}
    (hb : IsRetract b) (hu : typed u (arrowR a b)) :
    u = comp b u := by
  have hu' := typed_of_arrowR hu
  rw [hu']
  apply graph_ext
  intro x
  simp only [comp_app]
  rw [retract_app hb]

end DomainTheory.DataTypesAsLattices
