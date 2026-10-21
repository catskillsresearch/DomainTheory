/-ai
Application of the union of the graph of the finite element e p with the graph of the tagged successor at one more than the maximum of p and q, to the m-fold iterate of e p at e q, equals the successor iterate.

The proof rewrites by equation (2.9), the normalized finite application rule, and the tagged-successor rule. The no-tag rule, from the finite-iterate prohibition, drops the fresh tag, and simplification of bottom and of the iterate gives the successor iterate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_of_no_tag
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem finite_sigma_plain_app (p q m : ℕ) :
    funOf
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        (Z m (e p) (e q)) =
      Z (m + 1) (e p) (e q) := by
  rw [eq_2_9, normalized_finite_app, sigmaJ_app,
    sigmaJ_of_no_tag (fun k => Z_finite_no_tag p q m k)]
  simp [botElem, Z]

end DomainTheory.DataTypesAsLattices
