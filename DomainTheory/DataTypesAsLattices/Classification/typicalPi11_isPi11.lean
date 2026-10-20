/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace









































































































theorem typicalPi11_isPi11 : IsPi11 typicalPi11 :=
  ⟨fun u => u, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
