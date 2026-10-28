module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.expMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

noncomputable def arrowComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((lamComb a b).comp jArrow)

namespace arrowComb

theorem eq (a b : ApproximableMap U U) :
    arrowComb a b = iArrow.comp ((lamComb a b).comp jArrow) := rfl

theorem toElementMap (a b : ApproximableMap U U) (x : U.Element) :
    (arrowComb a b).toElementMap x =
      iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x)) := by
  rw [eq]
  simp only [toElementMap_comp]

theorem isRetraction {a b : ApproximableMap U U} (ha : Retraction a)
    (hb : Retraction b) : Retraction (arrowComb a b) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap a b ((arrowComb a b).toElementMap x),
    toElementMap a b x, toElementMap_of_comp_eq_idMap jArrow_comp_iArrow,
    toElementMap_idem_of_isRetraction (isRetraction_lamComb ha hb)]

theorem le_idMap {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    arrowComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap, toElementMap_idMap]
  calc iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x))
      ≤ iArrow.toElementMap (jArrow.toElementMap x) :=
        iArrow.toElementMap_mono
          (toElementMap_le_self_of_le_idMap (le_idMap_lamComb ha hb) _)
    _ ≤ x := toElementMap_le_of_comp_le_idMap iArrow_comp_jArrow_le x

theorem isProjection {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (arrowComb a b) :=
  ⟨isRetraction ha.1 hb.1, le_idMap ha.2 hb.2⟩

noncomputable def I (a b : ApproximableMap U U) :
    ApproximableMap (funSpace (fixedNbhd a) (fixedNbhd b)) U :=
  iArrow.comp (expMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).inj)

noncomputable def J (a b : ApproximableMap U U) :
    ApproximableMap U (funSpace (fixedNbhd a) (fixedNbhd b)) :=
  (expMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).proj).comp jArrow

theorem J_comp_I (a b : ApproximableMap U U) :
    (J a b).comp (I a b) = idMap (funSpace (fixedNbhd a) (fixedNbhd b)) := by
  unfold J I
  rw [comp_assoc, ← comp_assoc jArrow iArrow (expMap _ _), jArrow_comp_iArrow, idMap_comp,
    ← expMap.comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    expMap.id]

end arrowComb

end DomainTheory.NeighbourhoodSystems
