module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at `Γ`: `Γ g Z` forces `Z = Δ_E` (Scott's strictness). -/
theorem gRel_gamma_inv (hD : ∀ X, D.mem X → X.Nonempty) {Z}
    (h : GRel u v (Gamma D) Z) : Z = E.master := by
  generalize hW : Gamma D = W at h
  cases h with
  | gamma hZ => exact hZ
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_Gamma D hD X)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel => exact absurd hW.symm (embPair_ne_Gamma D hD P Q)

end Exercise717

end DomainTheory.NeighbourhoodSystems
