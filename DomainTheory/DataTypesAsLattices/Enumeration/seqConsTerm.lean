
module

public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seqCons
public import DomainTheory.DataTypesAsLattices.Enumeration.interp_avoids
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.envSet

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Term-level sequence cons constructor. -/
def seqConsTerm (a xs : Term) : Term :=
  .lam 7 (.cond (.var 7) a (.app xs (.pred (.var 7))))

namespace seqConsTerm

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem interp (a xs : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 7) (hxs : xs.Avoids 7) :
    interp (seqConsTerm a xs) ρ =
      seqCons (interp a ρ) (interp xs ρ) := by
  unfold seqConsTerm seqCons
  apply congrArg graph
  funext z
  simp only[_root_.DomainTheory.DataTypesAsLattices.interp]
  rw [interp_avoids a ρ z ha, interp_avoids xs ρ z hxs]
  simp[envSet, Function.update]

end seqConsTerm

end DomainTheory.DataTypesAsLattices
