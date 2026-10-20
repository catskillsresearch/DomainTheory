/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic
import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































theorem typicalFcapGdelta_isFcapGdelta : IsFcapGdelta typicalFcapGdelta :=
  (theorem_6_5 typicalFcapGdelta).mpr ⟨fun x => x, id_isScottContinuous, rfl⟩

end DomainTheory.DataTypesAsLattices
