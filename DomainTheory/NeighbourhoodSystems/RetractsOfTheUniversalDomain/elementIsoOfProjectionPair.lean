module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixedNbhd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.projPairToElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Cond
universe u
variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

def elementIsoOfProjectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    D.Element ≃o {y : E.Element // g.toElementMap y = y} where
  toFun x := ⟨i.toElementMap x, by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    rw [hg, toElementMap_comp, h1, hji, toElementMap_idMap]⟩
  invFun y := j.toElementMap y.1
  left_inv x := by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    show j.toElementMap (i.toElementMap x) = x
    rw [h1, hji, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : g.toElementMap y.1 = y.1 := y.2
    show i.toElementMap (j.toElementMap y.1) = y.1
    rw [← toElementMap_comp, ← hg]
    exact hfix
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := j.toElementMap_mono hle
      have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
        (toElementMap_comp j i x).symm
      have h2 : j.toElementMap (i.toElementMap x') = (j.comp i).toElementMap x' :=
        (toElementMap_comp j i x').symm
      rw [h1, h2, hji, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact i.toElementMap_mono hle

theorem inj_comp_proj_eq_self {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

theorem isFinitary_of_projectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    IsFinitary g :=
  ⟨α, D, ⟨(elementIsoOfProjectionPair i j hji hg).symm⟩⟩

theorem toElementMap_bot_eq_bot_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) : i.toElementMap D.bot = E.bot := by
  apply le_antisymm
  · calc i.toElementMap D.bot ≤ i.toElementMap (j.toElementMap E.bot) :=
          i.toElementMap_mono (D.bot_le _)
      _ ≤ E.bot := toElementMap_le_of_comp_le_idMap hij E.bot
  · exact E.bot_le _

end DomainTheory.NeighbourhoodSystems
