/-ai
The strict curry of a strict map out of the smash product relates a neighbourhood X to a strict-function neighbourhood exactly when the section of the map at X, which is strict, belongs to that neighbourhood. The domain, codomain, and master clauses are membership of X, membership of the neighbourhood, and the two master neighbourhoods. Intersection on the right uses closure of the strict function space under nonempty intersection, and monotonicity uses upward closure of its neighbourhoods together with monotonicity of the section in X. If X is the master, every output in the step list is the master, because the section collapses the smash pair to bottom and strictness of the original map forces that output, so the neighbourhood is the set of all strict maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.principal_master_eq_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_bot_left
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_iff_apply_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_inter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_up_closed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_smashSection

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Strict curry combinator.** `curry⊥ : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) → (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`, sending `g`
to `x ↦ (y ↦ g(⟨x, y⟩⊗))`. -/
def smashCurryMap (g : StrictMap (smash V₀ V₁) V₂) : StrictMap V₀ (strictFun V₁ V₂) :=
  ⟨{ rel := fun X N => ∃ hX : V₀.mem X, (strictFun V₁ V₂).mem N ∧
       (⟨smashSection g.1 hX, isStrict_smashSection g.2 hX⟩ : StrictMap V₁ V₂) ∈ N
     rel_dom := fun ⟨hX, _⟩ => hX
     rel_cod := fun ⟨_, hN, _⟩ => hN
     master_rel := ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
     inter_right := by
       rintro X N N' ⟨hX, hN, hmem⟩ ⟨_, hN', hmem'⟩
       exact ⟨hX, strictFun_mem_inter hN hN' ⟨_, hmem, hmem'⟩, Set.mem_inter hmem hmem'⟩
     mono := by
       rintro X X' N N' ⟨hX, hN, hmem⟩ hX'X hNN' hX' hN'
       refine ⟨hX', hN', strictFun_mem_up_closed hN' (hNN' hmem) ?_⟩
       exact Subtype.coe_le_coe.mp (smashSection_mono hX hX' hX'X) },
  by
    rintro N ⟨hΔ₀, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    have hall : ∀ p ∈ L, p.2 = V₂.master := by
      intro p hp
      have hpr : (smashSection g.1 hΔ₀).rel p.1 p.2 := hmem p hp
      rw [smashSection_rel] at hpr
      obtain ⟨hp1, hpmem⟩ := hpr
      have hbot : smashPair (V₀.principal hΔ₀) (V₁.principal hp1) = (smash V₀ V₁).bot := by
        rw [principal_master_eq_bot hΔ₀ rfl]; exact smashPair_bot_left _
      rw [hbot, isStrict_iff_apply_bot.mp g.2, NeighborhoodSystem.mem_bot] at hpmem
      exact hpmem
    apply Set.eq_univ_of_forall
    intro f q hq
    rw [hall q hq]
    exact (f.1).rel_master (hL q hq).1⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
