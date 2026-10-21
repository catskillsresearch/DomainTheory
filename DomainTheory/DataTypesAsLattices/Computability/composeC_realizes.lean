/-ai
If u realizes p and v realizes q, then their composition realizes the composite p ∘ q.

Rewrite by the definition of composition and the β-rules for S and K, then apply the two realization hypotheses.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4





theorem composeC_realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (composeC u v) (p ∘ q) := fun n => by
  rw [composeC, Scomb_beta3, Kcomb_beta2, hv n, hu (q n)]
  rfl

end DomainTheory.DataTypesAsLattices
