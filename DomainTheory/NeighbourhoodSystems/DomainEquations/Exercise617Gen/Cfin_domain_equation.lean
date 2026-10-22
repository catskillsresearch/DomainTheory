module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_domain_equation

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]


/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
