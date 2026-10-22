module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_subset_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.strBotN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjU_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sinjC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumMapSig_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigObj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tsigMapHom_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Tsig_map_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.toCC_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.fromCC_mem_embA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.ccEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cnobj_sys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.not_coneN_subset_singleton
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.liftCn

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

theorem liftCn_strBot (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strBotN σ) = coneVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := coneN_subset_coneN.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_coneN_subset_singleton σ σ')
  · intro hY
    exact ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

end Lift

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
