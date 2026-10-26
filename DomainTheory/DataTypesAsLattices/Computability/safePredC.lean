module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_2
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_bot
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λx. x ⊃ 0, x−1`, so numerals stay numerals. -/
def safePredC : Pomega :=
  interp (.lam 0 (.cond (.var 0) .zero (.pred (.var 0)))) (fun _ => botElem)

namespace safePredC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory : IsCombinatory safePredC :=
  theorem_2_4.closed _


theorem succ (n : ℕ) : funOf safePredC (ofNat (n + 1)) = ofNat n := by
  simp only [safePredC]
  rw [theorem_2_2.beta]
  simp [interp, envSet, Function.update, eq_2_7_succ, predSet.ofNat_succ]


theorem zero : funOf safePredC (ofNat 0) = ofNat 0 := by
  simp only [safePredC]
  rw [theorem_2_2.beta]
  simp [interp, envSet, Function.update, eq_2_7_zero]

end safePredC

end DomainTheory.DataTypesAsLattices
