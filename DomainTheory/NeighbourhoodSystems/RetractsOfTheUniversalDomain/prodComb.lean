module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

noncomputable def prodComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iTimes.comp ((paired (a.comp (proj₀ U U)) (b.comp (proj₁ U U))).comp jTimes)

namespace prodComb

theorem eq (a b : ApproximableMap U U) :
    prodComb a b = iTimes.comp ((prodMap a b).comp jTimes) := rfl

theorem toElementMap (a b : ApproximableMap U U) (x : U.Element) :
    (prodComb a b).toElementMap x =
      iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd)) := by
  rw [eq]
  simp only [toElementMap_comp, toElementMap_prodMap]

theorem isRetraction {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (prodComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap a b ((prodComb a b).toElementMap x),
    toElementMap a b x, toElementMap_of_comp_eq_idMap jTimes_comp_iTimes, fst_pair,
    snd_pair, toElementMap_idem_of_isRetraction ha, toElementMap_idem_of_isRetraction hb]

theorem le_idMap {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    prodComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap, toElementMap_idMap]
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

theorem isProjection {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (prodComb a b) :=
  ⟨isRetraction ha.1 hb.1, le_idMap ha.2 hb.2⟩

noncomputable def I (a b : ApproximableMap U U) :
    ApproximableMap (prod (fixedNbhd a) (fixedNbhd b)) U :=
  iTimes.comp (prodMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

noncomputable def J (a b : ApproximableMap U U) :
    ApproximableMap U (prod (fixedNbhd a) (fixedNbhd b)) :=
  (prodMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jTimes

theorem J_comp_I (a b : ApproximableMap U U) :
    (J a b).comp (I a b) = idMap (prod (fixedNbhd a) (fixedNbhd b)) := by
  unfold J I
  rw [comp_assoc, ← comp_assoc jTimes iTimes (prodMap _ _), jTimes_comp_iTimes, idMap_comp,
    ← prodMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    prodMap_id]

end prodComb

end DomainTheory.NeighbourhoodSystems
