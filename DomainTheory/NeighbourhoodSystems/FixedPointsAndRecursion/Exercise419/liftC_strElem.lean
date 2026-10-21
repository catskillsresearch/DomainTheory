/-ai
The lift sends each total element to the prescribed total value.

Extensionality reduces the equality to membership of a codomain neighbourhood. Such a neighbourhood is related to a domain neighbourhood that contains the singleton of the total element. If that neighbourhood is a cone, the singleton lies in the cone of a prefix, and the comparison of partial and total values carries the membership. If it is a singleton, the inclusion forces the two strings to agree, so the membership is already that of the prescribed value. Conversely, the singleton contains itself, is a neighbourhood of the total element, and is related to every neighbourhood of the prescribed value.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

/-- `liftC` on a total element: `f(σ) = singVal σ`. -/
theorem liftC_strElem (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strElem σ) = singVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_cone.mp
        rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at this
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise419
