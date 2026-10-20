/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
import DomainTheory.DataTypesAsLattices.Functionality.inleftC_app
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39


namespace DomainTheory.DataTypesAsLattices

































theorem typed_inleft_int_lamb {x : Pomega} (hx : typed x intR) :
    typed (funOf inleftC x) lambR := by
  rw [eq_4_39, inleftC_app]
  exact plusR_typed_inl hx

end DomainTheory.DataTypesAsLattices
