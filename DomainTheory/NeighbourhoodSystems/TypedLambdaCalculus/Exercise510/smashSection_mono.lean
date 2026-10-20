module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The section is monotone in the neighbourhood `X` (a smaller input gives a larger section). -/
theorem smashSection_mono {g : ApproximableMap (smash V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    smashSection g hX ≤ smashSection g hX' := by
  intro Y Z hrel
  obtain ⟨hY, hmem⟩ := hrel
  exact ⟨hY, toElementMap_mono g
    (smashPair_mono ((V₀.principal_le_iff hX hX').mpr hX'X) le_rfl) Z hmem⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
