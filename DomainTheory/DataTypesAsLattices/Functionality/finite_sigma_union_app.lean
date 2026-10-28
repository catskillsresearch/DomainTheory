module

public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_9
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_fresh_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem finite_sigma_union_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) ∪ {pair (max p q + 1) (m + 1)} := by
  rw [eq_2_9, normalized_finite_fresh_app, sigmaJ.app,
    sigmaJ.union_fresh (fun k => Z.finite_no_tag p q m k)]

end DomainTheory.DataTypesAsLattices
