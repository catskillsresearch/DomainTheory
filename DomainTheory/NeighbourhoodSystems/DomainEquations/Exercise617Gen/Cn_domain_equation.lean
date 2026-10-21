/-ai
The generic sequence domain over a decidable inhabited alphabet is isomorphic, as a domain, to the unit summed with one copy of itself for each letter.

The isomorphism is the packaged equivalence between the two sides.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]


/-- **Exercise 6.17 part 2 — the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
theorem Cn_domain_equation (A : Type) [DecidableEq A] [Inhabited A] :
    Cn A ≅ᴰ CCn A := ⟨ccEquiv⟩

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
