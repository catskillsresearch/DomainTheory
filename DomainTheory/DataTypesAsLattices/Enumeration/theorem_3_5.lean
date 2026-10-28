module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ecombinatory
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_codes
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ_more
public import DomainTheory.DataTypesAsLattices.Enumeration.Extensional
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillCase2Code
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillCase1Code
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum_more
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillCase1Code
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillCase2Code
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace theorem_3_5

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem case1 {u : Pomega} {p : ℕ → ℕ} {n k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : Extensional valNat p)
    (hk : k ∈ valNat (p n))
    (hnin : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)))
    (_hinf : ¬(valNat n).Finite) : False := by
  have hiff : ∀ m,
      k ∈ valNat (p (myhillCase1Code n m)) ↔ ¬∃ t, haltEnum t = m := by
    intro m
    by_cases hex : ∃ t, haltEnum t = m
    · have hfin : ({j | ∀ i ≤ j, haltEnum i ≠ m} : Pomega).Finite :=
        (Set.finite_Iio hex.choose).subset fun j hj =>
          Nat.lt_of_not_ge fun hle => hj hex.choose hle hex.choose_spec
      have hfins : (valNat (myhillCase1Code n m)).Finite := by
        rw [valNat.myhillCase1Code_eq]
        exact hfin.inter_of_right _
      obtain ⟨j, hj⟩ := exists_code_of_finite hfins
      have hje : e j ⊆ valNat n := by
        rw [hj, valNat.myhillCase1Code_eq]
        exact Set.inter_subset_left
      have : k ∉ valNat (p (fin j)) := fun h => hnin ⟨j, hje, h⟩
      have heq := hext.out (myhillCase1Code n m) (fin j) (by simp [hj, valNat.fin_eq])
      simp [heq, this, hex]
    · have hall : {j | ∀ i ≤ j, haltEnum i ≠ m} = Set.univ := by
        ext j
        constructor
        · intro _; trivial
        · intro _ i _
          exact fun h => hex ⟨i, h⟩
      have : valNat (myhillCase1Code n m) = valNat n := by
        rw [valNat.myhillCase1Code_eq, hall]
        simp
      have heq := hext.out (myhillCase1Code n m) n this
      simp [heq, hk, hex]
  have hre : REPred fun m => ¬∃ t, haltEnum t = m :=
    _root_.REPred.of_eq
      (valNat.mem_comp_primrec (k := k) hu hr (primrec_myhillCase1Code n))
      fun m => hiff m
  exact haltEnum.range_not_computable
    ((ComputablePred.computable_iff_re_compl_re').2 ⟨haltEnum.range_re, hre⟩)

theorem case2 {u : Pomega} {p : ℕ → ℕ} {n j k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p)
    (hext : Extensional valNat p)
    (hj : e j ⊆ valNat n)
    (_hne : e j ≠ valNat n)
    (hkfin : k ∈ valNat (p (fin j)))
    (hkn : k ∉ valNat (p n)) : False := by
  have hiff : ∀ m, k ∈ valNat (p (myhillCase2Code j n m)) ↔ valNat m = botElem := by
    intro m
    by_cases hm : valNat m = botElem
    · have : valNat (myhillCase2Code j n m) = e j := by
        rw [valNat.myhillCase2Code_eq, hm, eq_2_7_bot]
        simp [botElem]
      have := hext.out (myhillCase2Code j n m) (fin j) (by simp [this, valNat.fin_eq])
      simp [this, hkfin, hm]
    · have : valNat (myhillCase2Code j n m) = valNat n :=
        valNat.myhillCase2Code_ne_bot j n m hj hm
      have := hext.out (myhillCase2Code j n m) n this
      simp [this, hkn, hm]
  have hre : REPred fun m => valNat m = botElem :=
    _root_.REPred.of_eq
      (valNat.mem_comp_primrec (k := k) hu hr (primrec_myhillCase2Code j n))
      fun m => hiff m
  exact theorem_3_4 ⟨hre⟩

theorem of_realizer {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq

theorem q (val : ℕ → Pomega) (p : ℕ → ℕ) (j m : ℕ) :
    pair j m ∈ myhillQ val p ↔ m ∈ val (p (fin j)) := by
  constructor
  · intro ⟨j', m', hp, hm⟩
    obtain ⟨rfl, rfl⟩ := pair_inj hp
    exact hm
  · intro hm
    exact ⟨j, m, rfl, hm⟩

theorem q_app (p : ℕ → ℕ) (j : ℕ) :
    valNat (p (fin j)) ⊆ funOf (myhillQ valNat p) (e j) := by
  intro m hm
  exact ⟨j, subset_rfl, ⟨j, m, rfl, by simpa [valNat.fin_eq] using hm⟩⟩

theorem unique {q q' : Pomega → Pomega}
    (hq : IsScottContinuous q) (hq' : IsScottContinuous q')
    (h : ∀ n, q (e n) = q' (e n)) (x : Pomega) : q x = q' x := by
  rw [hq.out, hq'.out]
  ext k
  simp [scottUnion, scottPiece, h]

end theorem_3_5

theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : Extensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by
  obtain ⟨u, hu, hr⟩ := hp
  refine ⟨myhillQ valNat p, IsRE.combinatory (myhillQ.isRE hu hr), fun n => ?_⟩
  rw [myhillQ.app]
  ext k
  constructor
  · intro hk
    by_contra hnin
    have hinf : ∀ j, e j = valNat n → False := by
      intro j hj
      have : k ∈ valNat (p (fin j)) := by
        have := hext.out n (fin j) (by simp [valNat.fin_eq, hj])
        simpa [this, valNat.fin_eq] using hk
      exact hnin (Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨by simp [hj], this⟩⟩)

    have hfin : ¬(valNat n).Finite := by
      intro hf
      obtain ⟨j, hj⟩ := exists_code_of_finite hf
      exact hinf j hj
    have hnin' : ¬∃ j, e j ⊆ valNat n ∧ k ∈ valNat (p (fin j)) := by
      intro ⟨j, hj, hkj⟩
      exact hnin (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hkj⟩⟩)
    exact theorem_3_5.case1 hu hr hext hk hnin' hfin
  · intro hk
    obtain ⟨j, hk⟩ := Set.mem_iUnion.mp hk
    obtain ⟨hj, hk⟩ := Set.mem_iUnion.mp hk
    by_contra hnin
    have hne : e j ≠ valNat n := by
      intro hj'
      have := hext.out n (fin j) (by simp [valNat.fin_eq, hj'])
      exact hnin (by simpa [this, valNat.fin_eq] using hk)
    exact theorem_3_5.case2 hu hr hext hj hne hk hnin

end DomainTheory.DataTypesAsLattices
