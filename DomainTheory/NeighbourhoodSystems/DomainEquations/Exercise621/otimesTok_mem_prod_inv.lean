/-ai
If the product neighbourhood of X and Y belongs to the smash product and X is distinct from the left master, then X belongs to the left system and Y belongs to the right system.

If the neighbourhood is the master rectangle, injectivity of product neighbourhoods forces X to be the left master. If it is a proper rectangle, injectivity identifies the coordinates with members of the two systems.
ai-/
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













theorem otimesTok_mem_prod_inv {X Y : Set Str} (h : (otimesTok D₀ D₁).mem (prodTokNbhd X Y))
    (hX : X ≠ D₀.master) : D₀.mem X ∧ D₁.mem Y := by
  rcases h with heq | ⟨X', Y', hX', hY', -, -, heq⟩
  · obtain ⟨rfl, -⟩ := prodTokNbhd_injective heq; exact absurd rfl hX
  · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq; exact ⟨hX', hY'⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
