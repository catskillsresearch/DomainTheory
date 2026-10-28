module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.Subalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_1
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory_mem_subalgebra {A : Set Pomega} (hA : Subalgebra A)
    {u : Pomega} (hu : IsCombinatory u) : u ∈ A := by
  have hgen : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction hgen with
  | G => exact hA.out.1
  | app _ _ ih ih' => exact hA.out.2 ih ih'

end DomainTheory.DataTypesAsLattices
