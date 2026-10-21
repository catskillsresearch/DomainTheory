/-ai
The sum injection from the sum of the fixed neighbourhoods of a and b into the universal domain is the sum injection of the universal domain composed after the sum of the two subsystem injections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.fixedNbhd_mem_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section SumCase

variable (a b : ApproximableMap U U)

/-- **`I_+ : D_a + D_b → 𝒰`**, built by transporting `i₊` (Definition 8.9) through the functorial
action of `+` (Exercise 3.19's `sumMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def ISumComb : ApproximableMap (sum (fixedNbhd a) (fixedNbhd b)
    (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) U :=
  iPlus.comp (sumMap (h₀' := U_mem_nonempty) (h₁' := U_mem_nonempty)
    (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

end SumCase

end DomainTheory.NeighbourhoodSystems
