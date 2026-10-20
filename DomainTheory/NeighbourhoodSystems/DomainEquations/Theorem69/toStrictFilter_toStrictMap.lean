module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}






/-- `toStrictFilter ∘ toStrictMap = id` (the left inverse of the strict-function-space
representation; the mirror of `toStrictMap_toStrictFilter`). -/
theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hWmem, hfW⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
    exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
  · intro hW
    refine ⟨φ.sub hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
    intro p hp
    exact (mem_sstepFun_iff φ hL).mp hW p hp

end DomainTheory.NeighbourhoodSystems
