/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem expF_isScottContinuous : IsScottContinuous expF :=
  plus7_comp_isScottContinuous
    (const_isScottContinuous intR)
    (const_isScottContinuous botElem)
    id_isScottContinuous
    id_isScottContinuous
    tensor4_diag_isScottContinuous
    tensorR_diag_isScottContinuous
    (tensorR_right_isScottContinuous intR)

end DomainTheory.DataTypesAsLattices
