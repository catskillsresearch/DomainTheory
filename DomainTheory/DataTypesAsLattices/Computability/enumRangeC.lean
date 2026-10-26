module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_25
public import DomainTheory.DataTypesAsLattices.Computability.topElem_combinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def enumRangeC (r : Pomega) : Pomega :=
  (dollarC ⬝ r) ⬝ topElem

namespace enumRangeC

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem eq {r : Pomega} {p : ℕ → ℕ} (hr : Realizes r p) :
    enumRangeC r = ⋃ n, ofNat (p n) := by
  rw [enumRangeC, _root_.DomainTheory.DataTypesAsLattices.eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, _, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [hr n] using hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion₂.mpr ⟨n, Set.mem_univ n, by simpa [hr n] using hkn⟩

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem combinatory {r : Pomega} (hr : IsCombinatory r) :
    IsCombinatory (enumRangeC r) :=
  .app (.app dollarC.combinatory hr) topElem_combinatory

end enumRangeC

end DomainTheory.DataTypesAsLattices
