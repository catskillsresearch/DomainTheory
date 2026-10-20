/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.Definition71.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}






/-- **The one-point domain `𝟙` is effectively given.** -/
theorem unitSys_isEffectivelyGiven : unitSys.IsEffectivelyGiven :=
  ⟨unitPresentation⟩

end DomainTheory.Neighborhood
