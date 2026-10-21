/-ai
The product injection from the product of the fixed neighbourhoods of a and b into the universal domain is the product injection of the universal domain composed after the product of the two subsystem injections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

/-- **`I_× : D_a × D_b → 𝒰`**, built by transporting `i_×` (Definition 8.9) through the functorial
action of `×` (Exercise 3.19's `prodMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def IProdComb : ApproximableMap (prod (fixedNbhd a) (fixedNbhd b)) U :=
  iTimes.comp (prodMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

end ProdCase

end DomainTheory.NeighbourhoodSystems
