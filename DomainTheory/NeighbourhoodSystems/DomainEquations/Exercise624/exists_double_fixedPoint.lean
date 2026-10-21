/-ai
There is a pair of token sets, both containing the empty string, that solve the two coupled token equations at once: the token set of D summed with the product of D and E equals the first set, and the token set of the sum of D and E equals the second.

The two sets are Gamma_D and Gamma_E, using membership of the empty string in each and the two fixed-point equations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok_GammaD_GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok_GammaD_GammaE

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **The double fixed point (token level).** There is a pair of token sets `(Γ_D, Γ_E)`, both
containing `Λ`, that solve the two coupled token equations `tok(D + (D×E)) = Γ_D` and
`tok(D + E) = Γ_E` simultaneously. -/
theorem exists_double_fixedPoint :
    ∃ Γd Γe : Set Str, ([] : Str) ∈ Γd ∧ ([] : Str) ∈ Γe ∧
      fTok Γd Γe = Γd ∧ gTok Γd Γe = Γe :=
  ⟨GammaD, GammaE, nil_mem_GammaD, nil_mem_GammaE, fTok_GammaD_GammaE, gTok_GammaD_GammaE⟩

end Exercise624
end DomainTheory.NeighbourhoodSystems
