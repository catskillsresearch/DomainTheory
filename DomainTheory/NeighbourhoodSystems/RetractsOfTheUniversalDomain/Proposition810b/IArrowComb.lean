/-ai
The arrow injection from the function space of the fixed neighbourhood of a into the fixed neighbourhood of b, into the universal domain, is the arrow injection of the universal domain composed after the exponential that places the subsystem projection of a in the contravariant slot and the subsystem injection of b in the covariant slot.
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

/-- **`I_→ : (D_a → D_b) → 𝒰`**, built by transporting `i_→` (Definition 8.9) through the
functorial action of `→` (`expMap`) on `j_a : 𝒰 → D_a` (contravariant slot) and
`i_b : D_b → 𝒰` (covariant slot). -/
noncomputable def IArrowComb : ApproximableMap (funSpace (fixedNbhd a) (fixedNbhd b)) U :=
  iArrow.comp (expMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).inj)

end ArrowCase

end DomainTheory.NeighbourhoodSystems
