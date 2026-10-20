module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_dom
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.embZero_ne_embPair_of_memS

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at a leaf `0·X`: `0·X g Z ↔ X u Z`. -/
theorem gRel_embZero_inv (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α} {Z}
    (h : GRel u v (embZero X) Z) : u.rel X Z := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma hZ => exact absurd hW (embZero_ne_Gamma D hD X)
  | @leaf X' Z' hrel => rw [embZero_injective hW]; exact hrel
  | @node P Q Z₁ Z₂ Z hP hQ hvrel =>
      exact absurd hW (embZero_ne_embPair_of_memS hD (gRel_dom hP))

end Exercise717

end DomainTheory.NeighbourhoodSystems
