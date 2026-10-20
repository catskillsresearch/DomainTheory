/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 4.6 applied to (4.39).** -/
theorem lambR_isRetract : IsRetract lambR :=
  (theorem_4_6 lambF_isScottContinuous (fun _a ha =>
    plusR_isRetract intR_isRetract (arrowR_isRetract ha ha))).2

end DomainTheory.DataTypesAsLattices
