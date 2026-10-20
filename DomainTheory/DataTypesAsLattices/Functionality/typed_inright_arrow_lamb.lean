/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
import DomainTheory.DataTypesAsLattices.Functionality.inrightC_app
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39


namespace DomainTheory.DataTypesAsLattices

































theorem typed_inright_arrow_lamb {x : Pomega}
    (hx : typed x (arrowR lambR lambR)) :
    typed (funOf inrightC x) lambR := by
  rw [eq_4_39, inrightC_app]
  exact plusR_typed_inr hx

end DomainTheory.DataTypesAsLattices
