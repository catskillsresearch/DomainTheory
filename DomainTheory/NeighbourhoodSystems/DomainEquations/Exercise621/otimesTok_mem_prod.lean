module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem otimesTok_mem_prod {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y)
    (hXne : X ≠ D₀.master) (hYne : Y ≠ D₁.master) :
    (otimesTok D₀ D₁).mem (prodTokNbhd X Y) := Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
