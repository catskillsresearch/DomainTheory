/-ai
The fresh bottom of the lift is the element whose only neighbourhood is the lift master. That neighbourhood is the master, the only intersection is the master with itself, and any neighbourhood above the master equals the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- The **fresh bottom** of `𝒟_⊥`: the element whose only neighbourhood is the master `{Λ} ∪ 0Δ`. -/
def liftBot (D : NeighborhoodSystem Str) (hD : ∀ X, D.mem X → X.Nonempty) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D
  sub := by rintro W rfl; exact Or.inl rfl
  master_mem := rfl
  inter_mem := by rintro W W' rfl rfl; rw [Set.inter_self]
  up_mem := by
    rintro W W' rfl hW' hsub
    exact Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub

end Exercise619

end DomainTheory.NeighbourhoodSystems
