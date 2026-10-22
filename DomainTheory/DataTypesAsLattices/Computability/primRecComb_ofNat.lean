/-ai
Applying the primitive-recursion combinator of a base a and a step f to the numeral of n yields the n-fold primitive-recursion value of a and f.

Take the graph equation for the recursion step and the fixed-point theorem (2.5) for its Scott continuity. Rewriting by that graph, the fixed point, equation (2.27), and the evaluation of the recursion approximant on numerals gives the value.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem primRecComb_ofNat (a f : Pomega) (n : ℕ) :
    funOf (primRecComb a f) (ofNat n) = primRecVal a f n := by
  have hgraph := primRecStep_graph_of a f
  have hfix := theorem_2_5 (primRecStep_isScottContinuous a f)
  simp only [primRecComb]
  rw [← hgraph, hfix, ← eq_2_27, primRecHat_ofNat]

end DomainTheory.DataTypesAsLattices
