module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_proper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **The key computation.** For *proper* `X, Y`, `g(⟨↑X, ↑Y⟩⊗)` contains `Z` iff `g` relates the
proper neighbourhood `X ∪ Y` to `Z`. (Coarser members of the strict pairing are absorbed by
monotonicity; the master member needs only that `X ∪ Y ⊆ Δ₀ ∪ Δ₁`.) -/
theorem smashPair_principal_apply (g : ApproximableMap (smash V₀ V₁) V₂)
    {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) {Z : Set γ} :
    (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z
      ↔ g.rel (prodNbhd X Y) Z := by
  constructor
  · rintro ⟨W, hW, hrel⟩
    rcases hW with rfl | ⟨A, B, ⟨_, hXA⟩, _, ⟨_, hYB⟩, _, rfl⟩
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨hXA, hYB⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
  · intro hrel
    exact ⟨prodNbhd X Y, Or.inr ⟨X, Y, ⟨hX, subset_rfl⟩, hXne, ⟨hY, subset_rfl⟩, hYne, rfl⟩, hrel⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
