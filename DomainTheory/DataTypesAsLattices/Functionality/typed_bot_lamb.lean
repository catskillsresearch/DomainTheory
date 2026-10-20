/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_bot
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_39


namespace DomainTheory.DataTypesAsLattices

































theorem typed_bot_lamb : typed botElem lambR := by
  rw [eq_4_39]
  exact plusR_typed_bot _ _

end DomainTheory.DataTypesAsLattices
