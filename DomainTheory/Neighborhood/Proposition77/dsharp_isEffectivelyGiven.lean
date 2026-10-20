/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example61
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.Proposition77.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77











variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)













































variable (fcons feq finter : ℕ → ℕ)















/-- **Proposition 7.7 (Scott 1981, PRG-19).** If `D` is effectively given, so is `D^§`. -/
theorem dsharp_isEffectivelyGiven (P : ComputablePresentation D)
    (hD : ∀ X, D.mem X → X.Nonempty) :
    (Dsharp D hD).IsEffectivelyGiven :=
  ⟨dsharpPresentation P hD⟩

end Proposition77
end DomainTheory.Neighborhood
