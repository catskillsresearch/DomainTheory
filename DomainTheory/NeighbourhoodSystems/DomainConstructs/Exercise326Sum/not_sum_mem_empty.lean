module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSumEmb
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.condSum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_zeroset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_oneset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_left
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_masterC

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}


/-- `∅` is never a sum-neighbourhood (every neighbourhood is non-empty). -/
theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

end DomainTheory.NeighbourhoodSystems.Exercise326
