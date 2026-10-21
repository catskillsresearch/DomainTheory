/-ai
If A is a subalgebra and x and y belong to A, then the binary sequence constructor of x and y belongs to A.

The combinators S, K, cond, pred, and zero belong to A. Closing under application produces cond(x), then cond(y) applied to pred(zero), then S(K of that result) applied to pred, then S(K(cond x)) of that result, and the identity S K K. The SK equation rewrites the binary sequence constructor as S applied to the last two of these, which lies in A.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem seq2_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {x y : Pomega} (hx : x ∈ A) (hy : y ∈ A) : seq2 x y ∈ A := by
  have hS := combinatory_mem_subalgebra hA IsCombinatory.S
  have hK := combinatory_mem_subalgebra hA IsCombinatory.K
  have hcond := combinatory_mem_subalgebra hA IsCombinatory.cond
  have hpred := combinatory_mem_subalgebra hA IsCombinatory.pred
  have hzero := combinatory_mem_subalgebra hA IsCombinatory.zero
  have hbot := combinatory_mem_subalgebra hA bot_combinatory
  have hcondx := hA.2 hcond hx
  have hyb := hA.2 (hA.2 hcond hy) (hA.2 hpred hzero)
  have hinter := hA.2 (hA.2 hS (hA.2 hK hyb)) hpred
  have hF := hA.2 (hA.2 hS (hA.2 hK hcondx)) hinter
  have hI := hA.2 (hA.2 hS hK) hK
  rw [seq2_eq_SK]
  exact hA.2 (hA.2 hS hF) hI

end DomainTheory.DataTypesAsLattices
