/-ai
Scott 1976, Theorem 7.3 (ii). The combinator K lies in the function space from A to the function space from B to A.

K is a graph, and each application of K is a graph. On a related pair of second arguments, the double application law returns the original related pair in A.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.3 (ii).** `K : A → (B → A)`. -/
theorem theorem_7_3_ii (A B : RestrictedEquiv) :
    (arrowE A (arrowE B A)).mem Kcomb := by
  refine ⟨Kcomb_isGraph, Kcomb_isGraph, ?_⟩
  intro x x' hx
  refine ⟨Kcomb_app_isGraph x, Kcomb_app_isGraph x', ?_⟩
  intro y y' _hy
  simpa [Kcomb_app2] using hx

end DomainTheory.DataTypesAsLattices
