module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_12
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ProjPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section

open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

def IsUniversal {δ : Type w} (W : NeighborhoodSystem δ) : Prop :=
  ∀ {α : Type u} (D : NeighborhoodSystem α) [Countable {S : Set α // D.mem S}], D ⊴ W

theorem trianglelefteq_of_isomorphic_left {D : NeighborhoodSystem α} {D' : NeighborhoodSystem β}
    {E : NeighborhoodSystem γ} (hDD' : D ≅ᴰ D') (hD'E : D' ⊴ E) : D ⊴ E := by
  obtain ⟨F, hFE, ⟨eD'F⟩⟩ := hD'E
  obtain ⟨eDD'⟩ := hDD'
  exact ⟨F, hFE, ⟨eDD'.trans eD'F⟩⟩

theorem trianglelefteq_trans {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (h1 : D ⊴ E) (h2 : E ⊴ F) : D ⊴ F := by
  obtain ⟨D', hD'E, ⟨eDD'⟩⟩ := h1
  obtain ⟨E', hE'F, ⟨eEE'⟩⟩ := h2
  have pD'F : ProjPair D' F :=
    ((ProjPair.ofSubsystem hD'E).comp (ProjPair.ofIso eEE')).comp (ProjPair.ofSubsystem hE'F)
  have hD'F : D' ⊴ F :=
    trianglelefteq_of_projectionPair pD'F.inj pD'F.proj pD'F.proj_comp_inj pD'F.inj_comp_proj_le
  exact trianglelefteq_of_isomorphic_left ⟨eDD'⟩ hD'F

theorem U_isUniversal : IsUniversal.{u} U := by
  intro α D _
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

theorem funSpaceUU_trianglelefteq_U : funSpace U U ⊴ U :=
  trianglelefteq_of_projectionPair iArrow jArrow jArrow_comp_iArrow iArrow_comp_jArrow_le

theorem isUniversal_of_isomorphic {W : NeighborhoodSystem β} {W' : NeighborhoodSystem γ}
    (hW : IsUniversal.{u} W) (hWW' : W ≅ᴰ W') : IsUniversal.{u} W' := by
  have hWW'_tri : W ⊴ W' := hWW'.elim fun e => ⟨W', Subsystem.refl W', ⟨e⟩⟩
  intro α D _
  exact trianglelefteq_trans (hW D) hWW'_tri

theorem V.isUniversal : IsUniversal.{u} V :=
  isUniversal_of_isomorphic U_isUniversal ⟨effectiveIso812_UV.toDomainIso⟩

theorem prodUU_trianglelefteq_U : prod U U ⊴ U :=
  trianglelefteq_of_projectionPair iTimes jTimes jTimes_comp_iTimes iTimes_comp_jTimes_le

theorem sumUU_trianglelefteq_U : sum U U U_mem_nonempty U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iPlus jPlus jPlus_comp_iPlus iPlus_comp_jPlus_le

end

end DomainTheory.NeighbourhoodSystems
