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


/-- **`otimesMapTok` is always strict.** -/
theorem otimesMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (otimesMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, Y0, X', Y', -, -, hXne, -, -, -, heq, -⟩)
  · rfl
  · have heq' : prodTokNbhd A₀.sys.master A₁.sys.master = prodTokNbhd X Y0 := heq
    obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
    exact absurd h.symm hXne

end Exercise619
end DomainTheory.NeighbourhoodSystems
