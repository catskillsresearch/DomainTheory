/-ai
The section, at a neighbourhood of the first factor, of a strict map out of the smash product is itself strict.

Rewrite strictness as preservation of the bottom element, and unfold the section. The bottom element of the second system is the principal element of its master. The element map at that principal element, together with the right-hand bottom law, replaces the smash pair of the principal element of the given neighbourhood with the principal element of the master by the bottom element of the smash. What remains is preservation of the bottom element by the original map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_bot_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.IsStrict
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_iff_apply_bot
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

/-- The section of a *strict* `g` is itself strict: `g(⟨↑X, ⊥⟩⊗) = g(⊥) = ⊥`. -/
theorem isStrict_smashSection {g : ApproximableMap (smash V₀ V₁) V₂} (hg : IsStrict g)
    {X : Set α} (hX : V₀.mem X) : IsStrict (smashSection g hX) := by
  rw [isStrict_iff_apply_bot, smashSection,
    show (V₁.bot) = V₁.principal V₁.master_mem from rfl, toElementMap_ofMono_principal,
    show smashPair (V₀.principal hX) (V₁.principal V₁.master_mem) = (smash V₀ V₁).bot from
      smashPair_bot_right _]
  exact isStrict_iff_apply_bot.mp hg

end DomainTheory.NeighbourhoodSystems.Exercise510
