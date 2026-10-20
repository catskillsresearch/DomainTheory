/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise617
import DomainTheory.Neighborhood.Exercise617Gen.Basic


namespace DomainTheory.Neighborhood.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

variable {A : Type} [DecidableEq A]












































section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]













theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

end Iso
end DomainTheory.Neighborhood.Exercise617Gen
