/-ai
The domain of finite or infinite sequences over the alphabet Fin (n + 1) is isomorphic, as a domain, to the unit summed with one copy of itself for each letter of that alphabet.

The isomorphism is the generic domain equation instantiated at Fin (n + 1).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_domain_equation

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]





















































/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
