module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- `toStrictFilter` is monotone. -/
theorem toStrictFilter_mono {f f' : StrictMap V₀ V₁} (h : f ≤ f') :
    toStrictFilter f ≤ toStrictFilter f' := by
  intro W hW
  rw [mem_toStrictFilter] at hW ⊢
  exact ⟨hW.1, strictFun_mem_up_closed hW.1 hW.2 h⟩

end DomainTheory.NeighbourhoodSystems
