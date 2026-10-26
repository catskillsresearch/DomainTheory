
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.bot_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.union_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def unionBits : List ℕ → Pomega
  | [] => botElem
  | k :: ks => ofNat k ∪ unionBits ks

namespace unionBits

theorem eq : ∀ ks : List ℕ, unionBits ks = {n | n ∈ ks}
  | [] => by simp [unionBits, botElem]
  | k :: ks => by
    ext n
    simp [unionBits, eq ks, ofNat]

theorem combinatory : ∀ ks, IsCombinatory (unionBits ks)
  | [] => bot_combinatory
  | k :: ks => union_combinatory (ofNat.combinatory k) (combinatory ks)

end unionBits

end DomainTheory.DataTypesAsLattices
