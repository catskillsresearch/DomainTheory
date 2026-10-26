module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_more
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_more
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- `V` does not change already-closed points of a retract. -/
theorem typed_of_retract_Vcomb {a x : Pomega} (hx : typed x a) :
    typed x (funOf Vcomb a) := by
  rw [typed, Vcomb.app]
  have happ : funOf (graph (fun z => Vapply a z)) x = Vapply a x :=
    beta (Vapply.right_isScottContinuous a) x
  rw [happ]
  apply subset_antisymm
  · exact eq_5_16 a x
  · intro k hk
    exact hk x ⟨subset_rfl, by rw [← hx]⟩


end DomainTheory.DataTypesAsLattices
