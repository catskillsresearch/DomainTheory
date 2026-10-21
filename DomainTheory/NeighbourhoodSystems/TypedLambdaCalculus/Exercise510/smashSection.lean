/-ai
The section at a neighbourhood X of an approximable map out of the smash is the approximable map that sends the principal filter of a neighbourhood Y to the image of the strict pairing of the principal filter of X with the principal filter of Y. It is the monotone extension of those values, and the values are monotone because the image of a map and the strict pairing in its second argument are monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The `X`-section of `g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₂`, as a map `𝒟₁ → 𝒟₂`: `y ↦ g(⟨↑X, y⟩⊗)`. Built with
Exercise 2.8's `ofMono` from its values on principal inputs. -/
def smashSection (g : ApproximableMap (smash V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ :=
  ofMono (fun Y hY => g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY)))
    (by
      intro Y Y' hY hY' hY'Y
      exact toElementMap_mono g (smashPair_mono le_rfl ((V₁.principal_le_iff hY hY').mpr hY'Y)))

end DomainTheory.NeighbourhoodSystems.Exercise510
