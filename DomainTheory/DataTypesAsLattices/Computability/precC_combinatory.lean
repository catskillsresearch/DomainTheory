/-ai
If f and g are combinatory, then so is the primitive recursion built from them.

Rewrite by the completeness half of Theorem 2.4, and apply the combinatory interpretation of the recursion term in the environment of f and g.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.precEnv_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem precC_combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    IsCombinatory (precC f g) := by
  rw [precC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ (precEnv_combinatory hf hg)

end DomainTheory.DataTypesAsLattices
