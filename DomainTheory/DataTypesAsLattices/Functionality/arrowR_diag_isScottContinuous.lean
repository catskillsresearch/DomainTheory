/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
