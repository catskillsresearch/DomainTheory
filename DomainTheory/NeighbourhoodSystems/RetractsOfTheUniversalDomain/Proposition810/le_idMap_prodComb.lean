module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_le_of_comp_le_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_le_self_of_le_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_prodComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Proposition 8.10, `×`-case, projection half.** -/
theorem le_idMap_prodComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    prodComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_prodComb, toElementMap_idMap]
  have hpair : pair (a.toElementMap (jTimes.toElementMap x).fst)
      (b.toElementMap (jTimes.toElementMap x).snd)
      ≤ pair (jTimes.toElementMap x).fst (jTimes.toElementMap x).snd :=
    pair_le_pair_iff.mpr
      ⟨toElementMap_le_self_of_le_idMap ha _, toElementMap_le_self_of_le_idMap hb _⟩
  rw [pair_fst_snd] at hpair
  calc iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd))
      ≤ iTimes.toElementMap (jTimes.toElementMap x) := iTimes.toElementMap_mono hpair
    _ ≤ x := toElementMap_le_of_comp_le_idMap iTimes_comp_jTimes_le x

end DomainTheory.NeighbourhoodSystems
