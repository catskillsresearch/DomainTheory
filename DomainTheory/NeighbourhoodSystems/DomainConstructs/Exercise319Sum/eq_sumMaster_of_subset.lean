/-ai
A sum neighbourhood that contains the sum master is equal to the sum master.

Every sum neighbourhood is contained in the sum master, so that inclusion together with the given inclusion yields equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A sum-neighbourhood that *contains* the master is the master. -/
theorem eq_sumMaster_of_subset {W : Set (Option (α ⊕ β))}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : sumMaster V₀ V₁ ⊆ W) :
    W = sumMaster V₀ V₁ :=
  Set.Subset.antisymm ((sum V₀ V₁ h₀ h₁).sub_master hW) hsub

end DomainTheory.NeighbourhoodSystems
