/-ai
If u realizes p and v realizes q, then their pairing realizer realizes the function sending n to the pair of p(n) and q(n).

Rewrite by the definition, the β-rules for S and K, the two realization hypotheses, and the application equation for the pairing combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem pairRealizer_realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (pairRealizer u v) (fun n => Nat.pair (p n) (q n)) := fun n => by
  rw [pairRealizer, Scomb_beta3, Scomb_beta3, Kcomb_beta2,
    hu, hv, pairComb_app]

end DomainTheory.DataTypesAsLattices
