module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpTerm
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def primRecOpC : Pomega := interp primRecOpTerm primRecOpEnv

namespace primRecOpC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (a f : Pomega) :
    (primRecOpC ⬝ a) ⬝ f = primRecComb a f := by
  rw [primRecOpC, primRecOpTerm, theorem_2_2.beta, theorem_2_2.beta]
  simp [interp, envSet, Function.update, primRecOpEnv, primRecComb]

theorem combinatory : IsCombinatory primRecOpC := by
  rw [primRecOpC, theorem_2_4.complete]
  exact ofComb.combinatory _ _ primRecOpEnv.combinatory

end primRecOpC

end DomainTheory.DataTypesAsLattices
