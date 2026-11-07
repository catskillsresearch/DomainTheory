module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.projPairToElementMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.lamComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

noncomputable def iArrow : ApproximableMap (funSpace U U) U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose

noncomputable def iPlus : ApproximableMap (sum U U U_mem_nonempty U_mem_nonempty) U :=
  (theorem_8_8_b_strong sumUUPresentation).choose

noncomputable def iTimes : ApproximableMap (prod U U) U :=
  (theorem_8_8_b_strong prodUUPresentation).choose

noncomputable def jArrow : ApproximableMap U (funSpace U U) :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose

noncomputable def jPlus : ApproximableMap U (sum U U U_mem_nonempty U_mem_nonempty) :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose

noncomputable def jTimes : ApproximableMap U (prod U U) :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose

theorem iArrow_comp_jArrow_le : iArrow.comp jArrow ≤ idMap U :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.1

theorem iArrow_isComputableMap :
    ComputableMap funSpaceUUPresentation UComputablePresentation iArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.1

theorem iPlus_comp_jPlus_le : iPlus.comp jPlus ≤ idMap U :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.1

theorem iPlus_isComputableMap : ComputableMap sumUUPresentation UComputablePresentation iPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.1

theorem iTimes_comp_jTimes_le : iTimes.comp jTimes ≤ idMap U :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.1

theorem iTimes_isComputableMap :
    ComputableMap prodUUPresentation UComputablePresentation iTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.1

theorem jArrow_comp_iArrow : jArrow.comp iArrow = idMap _ :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.1

theorem jArrow_isComputableMap :
    ComputableMap UComputablePresentation funSpaceUUPresentation jArrow :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose_spec.2.2.2

theorem jPlus_comp_iPlus : jPlus.comp iPlus = idMap _ :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.1

theorem jPlus_isComputableMap : ComputableMap UComputablePresentation sumUUPresentation jPlus :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.2.2

theorem jTimes_comp_iTimes : jTimes.comp iTimes = idMap _ :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.1

theorem jTimes_isComputableMap :
    ComputableMap UComputablePresentation prodUUPresentation jTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.2

theorem definition_89 :
    jArrow.comp iArrow = idMap (funSpace U U) ∧
      jPlus.comp iPlus = idMap (sum U U U_mem_nonempty U_mem_nonempty) ∧
        jTimes.comp iTimes = idMap (prod U U) ∧
          iArrow.comp jArrow ≤ idMap U ∧
            iPlus.comp jPlus ≤ idMap U ∧
              iTimes.comp jTimes ≤ idMap U :=
  ⟨jArrow_comp_iArrow, jPlus_comp_iPlus, jTimes_comp_iTimes,
    iArrow_comp_jArrow_le, iPlus_comp_jPlus_le, iTimes_comp_jTimes_le⟩

end DomainTheory.NeighbourhoodSystems
