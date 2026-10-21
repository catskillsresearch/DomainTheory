/-ai
In the second case of Theorem 3.5, if a combinatory element realizes an extensional p, a finite set is contained in val(n), and k lies in the value of p at that finite code but not in val(p(n)), then falsehood follows.

For every m, k lies in the value of p at the second Myhill case code of the finite index, n, and m if and only if val(m) is bottom. If val(m) is bottom, the value of the case code equals the finite set, by the value equation and the bottom case of equation 2.7, so extensionality makes both sides hold. If val(m) is not bottom, the value of the case code equals val(n), so extensionality makes both sides fail. Membership of k in val of p, along the primitive recursive case code and the realizer, therefore agrees with the predicate that val(m) is bottom, so that predicate is recursively enumerable, contradicting Theorem 3.4. The hypothesis that the finite set is distinct from val(n) is not used.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillCase2Code
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code_ne_bot
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_comp_primrec

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem theorem_3_5_case2 {u : Pomega} {p : ℕ → ℕ} {n j k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : IsExtensional valNat p)
    (hj : e j ⊆ valNat n)
    (_hne : e j ≠ valNat n)
    (hkfin : k ∈ valNat (p (fin j)))
    (hkn : k ∉ valNat (p n)) : False := by
  have hiff : ∀ m, k ∈ valNat (p (myhillCase2Code j n m)) ↔ valNat m = botElem := by
    intro m
    by_cases hm : valNat m = botElem
    · have : valNat (myhillCase2Code j n m) = e j := by
        rw [valNat_myhillCase2Code, hm, eq_2_7_bot]
        simp [botElem]
      have := hext (myhillCase2Code j n m) (fin j) (by simp [this, valNat_fin])
      simp [this, hkfin, hm]
    · have : valNat (myhillCase2Code j n m) = valNat n :=
        valNat_myhillCase2Code_ne_bot j n m hj hm
      have := hext (myhillCase2Code j n m) n this
      simp [this, hkn, hm]
  have hre : REPred fun m => valNat m = botElem :=
    _root_.REPred.of_eq
      (valNat_mem_comp_primrec (k := k) hu hr (primrec_myhillCase2Code j n))
      fun m => hiff m
  exact theorem_3_4 hre

end DomainTheory.DataTypesAsLattices
