/-ai
Applying the curried primitive-recursion operator primRecOpC to an initial value a and a step f yields the primitive-recursion combinator primRecComb a f.

Unfold primRecOpC and primRecOpTerm, and apply the beta law theorem_2_2_beta twice. Simplifying the interpretation, the environment update, primRecOpEnv, and primRecComb gives the equality.
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

































theorem primRecOpC_app (a f : Pomega) :
    (primRecOpC ⬝ a) ⬝ f = primRecComb a f := by
  rw [primRecOpC, primRecOpTerm, theorem_2_2_beta, theorem_2_2_beta]
  simp [interp, envSet, Function.update, primRecOpEnv, primRecComb]

end DomainTheory.DataTypesAsLattices
