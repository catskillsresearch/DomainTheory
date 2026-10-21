/-ai
The section at a neighbourhood X of the uncurry of a strict map into the strict function space relates a neighbourhood Y to a set Z exactly when the original map relates X to the step set of Y and Z.

After the section criterion, the argument splits on whether the neighbourhoods are masters. If X is the master, the smash pair of the two principals is bottom, so strictness of the uncurry forces Z to be the master; the step with master codomain is everything, and the map relates X to the master. Conversely, strictness makes that step the universe, the constantly bottom strict map lies in it, and membership of bottom forces Z to be the master, after which the section contains the master. If Y is the master and X is proper, the same collapse uses the right factor, the step of the two masters is everything, and a witness in the step forces Z to be the master. If both are proper, application of the map to the smash pair of the two principals converts membership of Z into a relation on the product neighbourhood, and the two preimages of a product neighbourhood recover X and Y.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_proper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_eq_bot_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.principal_master_eq_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_iff_apply_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_constBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_principal_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_cod_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **The decisive computation for the adjunction.** The `X`-section of `uncurry⊥ h` evaluated on a
neighbourhood `Y` is exactly the strict-function value `X h [Y, Z]`. At the boundary (a master
factor) both sides collapse via strictness; off the boundary it is `smashPair_principal_apply`. -/
theorem section_uncurry_rel (h : StrictMap V₀ (strictFun V₁ V₂))
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    (smashSection (smashUncurryMap h).1 hX).rel Y Z ↔ h.1.rel X (sstep Y Z) := by
  rw [smashSection_rel]
  by_cases hXm : X = V₀.master
  · subst hXm
    constructor
    · rintro ⟨hY', hmem⟩
      rw [principal_master_eq_bot hX rfl,
        show smashPair V₀.bot (V₁.principal hY') = (smash V₀ V₁).bot from
          smashPair_eq_bot_iff.mpr (Or.inl rfl),
        isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
      subst hmem
      rw [sstep_cod_master hY]
      exact h.1.rel_master hX
    · intro hrel
      have huniv : sstep Y Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
      have hZ : Z = V₂.master := by
        have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep Y Z := by
          rw [huniv]; exact Set.mem_univ _
        obtain ⟨_, hbz⟩ := hcb
        rwa [NeighborhoodSystem.mem_bot] at hbz
      subst hZ
      exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
  · by_cases hYm : Y = V₁.master
    · subst hYm
      constructor
      · rintro ⟨hY', hmem⟩
        rw [principal_master_eq_bot hY' rfl,
          show smashPair (V₀.principal hX) V₁.bot = (smash V₀ V₁).bot from
            smashPair_eq_bot_iff.mpr (Or.inr rfl),
          isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
        subst hmem
        rw [sstep_master_eq]
        exact h.1.rel_master hX
      · intro hrel
        obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
        have hZ : Z = V₂.master := f.2 hf
        subst hZ
        exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
    · constructor
      · rintro ⟨hY', hmem⟩
        obtain ⟨_, hrel⟩ :=
          (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mp hmem
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel
      · intro hrel
        refine ⟨hY, (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mpr ?_⟩
        refine ⟨smash_mem_proper hX hXm hY hYm, ?_⟩
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel

end DomainTheory.NeighbourhoodSystems.Exercise510
