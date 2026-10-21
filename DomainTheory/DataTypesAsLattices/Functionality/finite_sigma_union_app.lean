/-ai
The same union, applied to that iterate adjoined with the singleton of the pair of the fresh tag and m, equals the successor iterate adjoined with the singleton of the pair of that tag and m + 1.

The proof rewrites by equation (2.9), the normalized finite application rule for a fresh tag, and the tagged-successor rule, then uses the union rule for a fresh tag from the finite-iterate prohibition.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_union_fresh
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_fresh_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem finite_sigma_union_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) ∪ {pair (max p q + 1) (m + 1)} := by
  rw [eq_2_9, normalized_finite_fresh_app, sigmaJ_app,
    sigmaJ_union_fresh (fun k => Z_finite_no_tag p q m k)]

end DomainTheory.DataTypesAsLattices
