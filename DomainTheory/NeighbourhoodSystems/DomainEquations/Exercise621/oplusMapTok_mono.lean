module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- `oplusMapTok` is monotone in both arguments. -/
theorem oplusMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    oplusMapTok f₀ f₁ ≤ oplusMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ |
    ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, hXne, hX'ne, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end DomainTheory.NeighbourhoodSystems
