/-ai
For finitary projections a and b, the sum injection into the universal domain composed after the sum extraction equals the sum combinator of a and b.

Unfold both maps. Associativity, the composition law of the sum of maps, the identities that each subsystem injection after its projection is the finitary projection, and the identification of the sum combinator with the sum injection after the sum of the maps after the sum extraction give the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.inj_comp_proj_eq_self
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.sumComb_eq_iPlus_sumMap_jPlus
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

theorem ISumComb_comp_JSumComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (ISumComb a b).comp (JSumComb a b) = sumComb a b := by
  unfold ISumComb JSumComb
  rw [comp_assoc, ← comp_assoc (sumMap _ _) (sumMap _ _) jPlus, ← sumMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc,
    sumComb_eq_iPlus_sumMap_jPlus, comp_assoc]

end SumCase

end DomainTheory.NeighbourhoodSystems
