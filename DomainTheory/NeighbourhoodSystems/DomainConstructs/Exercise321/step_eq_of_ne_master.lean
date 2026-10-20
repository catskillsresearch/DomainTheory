module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_master_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_eq_univ_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep_eq_of_step_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}









/-- **Exercise 3.21 (Scott 1981, PRG-19).** If `Z ≠ Δ₂`, the neighbourhood `[Y, Z]` determines both
endpoints: `[Y, Z] = [Y', Z']` implies `Y = Y'` and `Z = Z'`. -/
theorem step_eq_of_ne_master {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') (hZne : Z ≠ V₁.master)
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') : Y = Y' ∧ Z = Z' := by
  -- `Z' ≠ Δ₂` too, else `[Y', Z']` is the whole space and so is `[Y, Z]`, forcing `Z = Δ₂`
  have hZ'ne : Z' ≠ V₁.master := by
    intro hZ'eq
    rw [hZ'eq, step_master_right Y' hY'] at h
    exact hZne ((step_eq_univ_iff hY hZ).mp h)
  have hfeq := leastStep_eq_of_step_eq hY hZ hY' hZ' h
  -- `f₀.rel Y' Z'` and `f₀'.rel Y Z`, both with non-master outputs
  have h1 : (leastStep Y Z hY hZ).rel Y' Z' := by
    rw [hfeq]; exact (leastStep_mem hY' hZ')
  have h2 : (leastStep Y' Z' hY' hZ').rel Y Z := by
    rw [← hfeq]; exact (leastStep_mem hY hZ)
  rw [leastStep_rel hY hZ hY' hZ'] at h1
  rw [leastStep_rel hY' hZ' hY hZ] at h2
  -- from `h1`: `Y' ⊆ Y` and `Z ⊆ Z'`
  have hY'Y : Y' ⊆ Y := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h1
    exact hZ'ne (Set.Subset.antisymm (V₁.sub_master hZ') h1)
  have hZZ' : Z ⊆ Z' := by
    rw [interYs_single_subset_eq hZ hY'Y] at h1; exact h1
  -- from `h2`: `Y ⊆ Y'` and `Z' ⊆ Z`
  have hYY' : Y ⊆ Y' := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h2
    exact hZne (Set.Subset.antisymm (V₁.sub_master hZ) h2)
  have hZ'Z : Z' ⊆ Z := by
    rw [interYs_single_subset_eq hZ' hYY'] at h2; exact h2
  exact ⟨Set.Subset.antisymm hYY' hY'Y, Set.Subset.antisymm hZZ' hZ'Z⟩

end DomainTheory.NeighbourhoodSystems
