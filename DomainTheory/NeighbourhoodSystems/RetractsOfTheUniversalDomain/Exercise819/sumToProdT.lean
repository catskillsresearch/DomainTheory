/-ai
The tagging embedding from the sum of E with itself into the product of the three-point domain with the product of E with itself sends a sum element to the triple consisting of its tag, its left output, and its right output.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)

/-- **The tagging embedding `E + E → T × (E × E)`.** `w ↦ (which w, out₀ w, out₁ w)`. -/
noncomputable def sumToProdT : ApproximableMap (sum E E hE hE) (prod TD (prod E E)) :=
  paired (whichMap E E hE hE)
    (paired (outMap₀ (h₀ := hE) (h₁ := hE)) (outMap₁ (h₀ := hE) (h₁ := hE)))

end Sum

end DomainTheory.NeighbourhoodSystems
