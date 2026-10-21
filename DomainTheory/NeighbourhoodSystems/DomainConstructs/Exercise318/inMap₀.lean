/-ai
The left injection is the approximable map from the first neighbourhood system to the sum that relates a neighbourhood X to a sum neighbourhood W when the left copy of X is contained in W. The masters are related because a left copy of a neighbourhood lies in the sum master. Intersection on the right intersects the sum neighbourhoods, with the left copy of X as the consistency witness, and monotonicity uses that the left copy preserves inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀_subset_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left injection `in₀ : 𝒟₀ → 𝒟₀ + 𝒟₁`,
`X (in₀) W ↔ 0X ⊆ W`. -/
def inMap₀ : ApproximableMap V₀ (sum V₀ V₁ h₀ h₁) where
  rel X W := V₀.mem X ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

end DomainTheory.NeighbourhoodSystems
