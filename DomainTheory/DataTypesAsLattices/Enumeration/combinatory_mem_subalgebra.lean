/-ai
Every combinatory element lies in every subalgebra.

Theorem 3.1 converts the combinatory hypothesis into generation from G. Induct on that generation. The generator belongs to the subalgebra, and an application belongs to it by closure under application.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory_mem_subalgebra {A : Set Pomega} (hA : IsSubalgebra A)
    {u : Pomega} (hu : IsCombinatory u) : u ∈ A := by
  have hgen : GeneratedFromG u := (theorem_3_1 (u := u)).mp hu
  clear hu
  induction hgen with
  | G => exact hA.1
  | app _ _ ih ih' => exact hA.2 ih ih'

end DomainTheory.DataTypesAsLattices
