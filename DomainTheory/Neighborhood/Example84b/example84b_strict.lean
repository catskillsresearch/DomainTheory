/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example84
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Example84b.Basic
import DomainTheory.Neighborhood.Example84b.isRetraction_strictRetraction
import DomainTheory.Neighborhood.Example84b.strictRetraction_le_idMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







section Strict











/-- **Example 8.4(b)(i) (Scott 1981, PRG-19).** `strictRetraction` is a projection on `D → E`
whose fixed-point set is isomorphic to the strict function space `Exercise510.strictFun D E`. -/
theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩

end Strict
end DomainTheory.Neighborhood
