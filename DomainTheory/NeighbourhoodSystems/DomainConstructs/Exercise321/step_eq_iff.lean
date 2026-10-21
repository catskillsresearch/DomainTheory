/-ai
The step neighbourhood of a pair of neighbourhoods equals the step neighbourhood of another pair if and only if both outputs are the master neighbourhood, or the two pairs coincide.

If the steps are equal and the first output is the master, the first step is the whole function space, so the second step is the whole space and its output is the master. If the first output is not the master, equality of steps forces the two inputs and the two outputs to agree. Conversely, when both outputs are the master both steps are the whole space, and when the pairs coincide the steps are the same neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_master_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_eq_univ_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_eq_of_ne_master

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 3.21 (Scott 1981, PRG-19).** The simple criterion for identity of function-space
neighbourhoods: `[Y, Z] = [Y', Z']` iff both outputs are the master `Δ₂`, or the pairs coincide. -/
theorem step_eq_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' ↔
      (Z = V₁.master ∧ Z' = V₁.master) ∨ (Y = Y' ∧ Z = Z') := by
  constructor
  · intro h
    by_cases hZeq : Z = V₁.master
    · refine Or.inl ⟨hZeq, ?_⟩
      rw [hZeq, step_master_right Y hY] at h
      exact (step_eq_univ_iff hY' hZ').mp h.symm
    · exact Or.inr (step_eq_of_ne_master hY hZ hY' hZ' hZeq h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [step_master_right Y hY, step_master_right Y' hY']
    · rfl

end DomainTheory.NeighbourhoodSystems
