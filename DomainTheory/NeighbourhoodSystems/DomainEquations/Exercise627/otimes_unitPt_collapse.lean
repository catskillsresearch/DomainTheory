/-ai
Every neighbourhood of the smash of the two-point domain with the one-point unit equals the master of that smash.

The master case is reflexivity. A proper smash neighbourhood would require a neighbourhood of the unit distinct from the unit master, but membership in the unit is equality with its master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}





















/-- With the unit second factor, the smash `twoPt ⊗ 𝟙` collapses to its master. -/
theorem otimes_unitPt_collapse :
    ∀ W, (otimesTok twoPt unitPt).mem W → W = (otimesTok twoPt unitPt).master := by
  rintro W (rfl | ⟨X, Y, _, hY, _, hYne, rfl⟩)
  · rfl
  · exact absurd hY hYne

end Exercise627
end DomainTheory.NeighbourhoodSystems
