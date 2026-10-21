/-ai
The product extraction composed after the product injection is the identity of the product of the two fixed neighbourhoods.

Unfold both maps. Associativity, the identity that the product extraction after the product injection is the identity, the composition law of the product of maps, the two subsystem identities that the projection after the injection is the identity, and the identity law of the product of maps give the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.prodMap_comp
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.prodMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

theorem JProdComb_comp_IProdComb :
    (JProdComb a b).comp (IProdComb a b) = idMap (prod (fixedNbhd a) (fixedNbhd b)) := by
  unfold JProdComb IProdComb
  rw [comp_assoc, ← comp_assoc jTimes iTimes (prodMap _ _), jTimes_comp_iTimes, idMap_comp,
    ← prodMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    prodMap_id]

end ProdCase

end DomainTheory.NeighbourhoodSystems
