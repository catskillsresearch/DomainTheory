/-ai
Scott 1976, Theorem 7.4 (i). For every restricted equivalence A and every n, the iterator Z_n lies in the function space from A → A to A → A.

The combinator and each of its applications are graphs. On a related pair, the iteration relation for Z, fed by preservation under the function argument, is the application law for the combinator.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_rel
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.4 (i).** `Zₙ : (A → A) → (A → A)`. -/
theorem theorem_7_4_i (A : RestrictedEquiv) (n : ℕ) :
    (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n) := by
  refine ⟨Zcomb_isGraph n, Zcomb_isGraph n, ?_⟩
  intro f f' hf
  refine ⟨Zcomb_app_isGraph n f, Zcomb_app_isGraph n f', ?_⟩
  intro x y hxy
  simpa [Zcomb_app2] using Z_rel A n hf.2.2 hxy

end DomainTheory.DataTypesAsLattices
