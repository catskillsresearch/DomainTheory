/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.expF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 4.6 applied to (4.44).** -/
theorem expR_isRetract : IsRetract expR :=
  (theorem_4_6 expF_isScottContinuous (fun _a ha =>
    plus7_isRetract intR_isRetract bot_isRetract ha ha
      (tensor4_isRetract ha ha ha ha) (tensorR_isRetract ha ha)
      (tensorR_isRetract intR_isRetract ha))).2

end DomainTheory.DataTypesAsLattices
