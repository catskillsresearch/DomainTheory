/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.arrowR_diag_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem lambF_isScottContinuous : IsScottContinuous lambF :=
  theorem_1_3 (f := fun b => plusR intR b) (g := fun z => arrowR z z)
    (plusR_right_isScottContinuous intR)
    arrowR_diag_isScottContinuous

end DomainTheory.DataTypesAsLattices
