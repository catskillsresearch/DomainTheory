/-ai
The arrow extraction from the universal domain into the function space of the fixed neighbourhood of a and the fixed neighbourhood of b is the exponential that places the subsystem injection of a in the contravariant slot and the subsystem projection of b in the covariant slot, composed after the arrow extraction of the universal domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.expMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ArrowCase

variable (a b : ApproximableMap U U)

/-- **`J_→ : 𝒰 → (D_a → D_b)`**, symmetric to `IArrowComb`, via `i_a` (contravariant) and
`j_b` (covariant). -/
noncomputable def JArrowComb : ApproximableMap U (funSpace (fixedNbhd a) (fixedNbhd b)) :=
  (expMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).proj).comp jArrow

end ArrowCase

end DomainTheory.NeighbourhoodSystems
