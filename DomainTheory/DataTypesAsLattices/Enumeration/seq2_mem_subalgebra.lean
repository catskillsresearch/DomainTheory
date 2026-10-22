
module

public import Mathlib.Computability.Halting
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


theorem seq2_mem_subalgebra {A : Set Pomega} (hA : Subalgebra A)
    {x y : Pomega} (hx : x ∈ A) (hy : y ∈ A) : seq2 x y ∈ A := by
  have hS := combinatory_mem_subalgebra hA IsCombinatory.S
  have hK := combinatory_mem_subalgebra hA IsCombinatory.K
  have hcond := combinatory_mem_subalgebra hA IsCombinatory.cond
  have hpred := combinatory_mem_subalgebra hA IsCombinatory.pred
  have hzero := combinatory_mem_subalgebra hA IsCombinatory.zero
  have hbot := combinatory_mem_subalgebra hA bot_combinatory
  have hcondx := hA.out.2 hcond hx
  have hyb := hA.out.2 (hA.out.2 hcond hy) (hA.out.2 hpred hzero)
  have hinter := hA.out.2 (hA.out.2 hS (hA.out.2 hK hyb)) hpred
  have hF := hA.out.2 (hA.out.2 hS (hA.out.2 hK hcondx)) hinter
  have hI := hA.out.2 (hA.out.2 hS hK) hK
  rw [seq2_eq_SK]
  exact hA.out.2 (hA.out.2 hS hF) hI

end DomainTheory.DataTypesAsLattices
