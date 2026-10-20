module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `[X, Y] ∩ [X, Y'] = [X, Y ∩ Y']` (intersectivity in the output). -/
theorem step_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (step X Y ∩ step X Y' : Set (ApproximableMap V₀ V₁)) = step X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_step]
  constructor
  · rintro ⟨h, h'⟩; exact f.inter_right h h'
  · intro h
    exact ⟨f.mono h subset_rfl Set.inter_subset_left (f.rel_dom h) hY,
           f.mono h subset_rfl Set.inter_subset_right (f.rel_dom h) hY'⟩

end DomainTheory.NeighbourhoodSystems
