/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88d
import DomainTheory.Neighborhood.Theorem88c
import DomainTheory.Neighborhood.Theorem88e.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)





























/-- **Theorem 8.8(b)(vii)(3), isomorphism half.** `D ≅ᴰ D''`. -/
theorem isomorphic_DprimeUCode : D ≅ᴰ DprimeUCode P := ⟨domainIsoCode P⟩

end DomainTheory.Neighborhood
