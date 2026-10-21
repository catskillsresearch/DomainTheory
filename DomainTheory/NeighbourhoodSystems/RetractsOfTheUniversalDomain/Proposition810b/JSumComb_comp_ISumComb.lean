/-ai
The sum extraction composed after the sum injection is the identity of the sum of the two fixed neighbourhoods.

Unfold both maps. Associativity, the identity that the sum extraction after the sum injection is the identity, the composition law of the sum of maps, the two subsystem identities that the projection after the injection is the identity, and the identity law of the sum of maps give the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.fixedNbhd_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.ISumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JSumComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section SumCase

variable (a b : ApproximableMap U U)

theorem JSumComb_comp_ISumComb :
    (JSumComb a b).comp (ISumComb a b) =
      idMap (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
        (fixedNbhd_mem_nonempty b)) := by
  unfold JSumComb ISumComb
  rw [comp_assoc, ← comp_assoc jPlus iPlus (sumMap _ _), jPlus_comp_iPlus, idMap_comp,
    ← sumMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    sumMap_id]

end SumCase

end DomainTheory.NeighbourhoodSystems
