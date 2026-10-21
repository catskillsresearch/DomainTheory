/-ai
The four-fold tensor of four retracts is a retract.

Unfold the retract equation and compare graphs. On an argument u, two applications of the tensor and the four component laws of the four-way sequence reduce the value to the four retract applications, which fix the four components.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensor4_isRetract {a b c d : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c) (hd : IsRetract d) :
    IsRetract (tensor4 a b c d) := by
  change tensor4 a b c d =
    graph (fun u => funOf (tensor4 a b c d) (funOf (tensor4 a b c d) u))
  apply graph_ext
  intro u
  rw [tensor4_app, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
    seq4_app_three, retract_app ha, retract_app hb, retract_app hc, retract_app hd]

end DomainTheory.DataTypesAsLattices
