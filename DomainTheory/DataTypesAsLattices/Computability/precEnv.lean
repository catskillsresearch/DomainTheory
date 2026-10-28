module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC
public import DomainTheory.DataTypesAsLattices.Computability.pack4

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def precEnv (f g : Pomega) : ℕ → Pomega
  | 3 => primRecOpC
  | 4 => f
  | 5 => g
  | 6 => unpairFstC
  | 7 => unpairSndC
  | 8 => pairComb
  | _ => botElem

namespace precEnv

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    ∀ i, IsCombinatory (precEnv f g i)
  | 3 => primRecOpC.combinatory
  | 4 => hf
  | 5 => hg
  | 6 => unpairFstC.combinatory
  | 7 => unpairSndC.combinatory
  | 8 => pairComb.combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 9 => botElem_combinatory

end precEnv

end DomainTheory.DataTypesAsLattices
