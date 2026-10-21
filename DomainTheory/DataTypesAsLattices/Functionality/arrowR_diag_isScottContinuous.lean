/-ai
The diagonal of the function-space retract, sending z to the arrow from z to z, is Scott-continuous.

Constancy of graphs under Scott continuity applies. For each fixed u, the map sending z to the graph of x mapped to the application of z to the application of u to the application of z at x is Scott-continuous by the same principle. Each section in x is continuous on the diagonal by the binary continuity package, whose factors are left continuity of application at the inner value and Theorem 1.3 applied to continuity of application of z and to Theorem 1.3 of continuity of application of u with left continuity of application at x, with both diagonal arguments the identity. Converting that statement, and comparing graphs by graph extensionality together with composition of application, identifies it with the diagonal of the arrow.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem arrowR_diag_isScottContinuous :
    IsScottContinuous (fun z => arrowR z z) := by
  apply graph_const_isScottContinuous
  intro u
  have h :
      IsScottContinuous (fun z =>
        graph (fun x => funOf z (funOf u (funOf z x)))) :=
    graph_const_isScottContinuous
      (fun z x => funOf z (funOf u (funOf z x)))
      (fun x =>
        continuous_tuple
          (fun y => funOf_isScottContinuous_left (funOf u (funOf y x)))
          (fun z =>
            theorem_1_3 (funOf_isScottContinuous z)
              (theorem_1_3 (funOf_isScottContinuous u)
                (funOf_isScottContinuous_left x)))
          id_isScottContinuous
          id_isScottContinuous)
  convert h using 1
  funext z
  apply graph_ext
  intro x
  simp only [comp_app]

end DomainTheory.DataTypesAsLattices
