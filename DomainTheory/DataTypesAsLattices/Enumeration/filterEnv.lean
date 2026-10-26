module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Lambda.predC
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def filterEnv : ℕ → Pomega
  | 3 => filterRealizer
  | 4 => pairComb
  | 5 => dollarC
  | 6 => predC
  | 7 => topElem
  | _ => botElem

namespace filterEnv

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem combinatory : ∀ i, IsCombinatory (filterEnv i)
  | 3 => filterRealizer.combinatory
  | 4 => pairComb.combinatory
  | 5 => dollarC.combinatory
  | 6 => .pred
  | 7 => topElem_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 8 => botElem_combinatory

end filterEnv

end DomainTheory.DataTypesAsLattices
