module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem sstep_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (sstep X Y ∩ sstep X Y' : Set (StrictMap V₀ V₁)) = sstep X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_sstep]
  constructor
  · rintro ⟨h, h'⟩; exact f.1.inter_right h h'
  · intro h
    exact ⟨f.1.mono h subset_rfl Set.inter_subset_left (f.1.rel_dom h) hY,
           f.1.mono h subset_rfl Set.inter_subset_right (f.1.rel_dom h) hY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
