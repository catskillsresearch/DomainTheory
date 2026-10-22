module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.eq_of_le_one_iff_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.primrec_matchesBCatGLookup

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


set_option maxHeartbeats 4000000 in
theorem primrec_matchesBCharBodyLookup : Nat.Primrec matchesBCharBodyLookup := by
  have htable : Nat.Primrec (fun w => w.unpair.1) := Nat.Primrec.left
  have hc : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hcw : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have htag : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.1) := Nat.Primrec.left.comp hc
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  have h23 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) htag)
  have h34 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) htag)
  have hf1 : Nat.Primrec (fun w => listEqChar w.unpair.2.unpair.2 w.unpair.2.unpair.1.unpair.2) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hcw (Nat.Primrec.right.comp hc))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun w'' => matchesBCatGLookup
      (Nat.pair w''.unpair.2.unpair.1 (Nat.pair w''.unpair.1 w''.unpair.2.unpair.2))) :=
    (primrec_matchesBCatGLookup.comp (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right)
      (Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.right.comp Nat.Primrec.right)))).of_eq
      fun _ => rfl
  have hcatpack : Nat.Primrec (fun w => Nat.pair
      (Nat.pair w.unpair.1 (Nat.pair w.unpair.2.unpair.1 w.unpair.2.unpair.2))
      (listLenChar w.unpair.2.unpair.2 + 1)) :=
    Nat.Primrec.pair (Nat.Primrec.pair htable (Nat.Primrec.pair hc hcw))
      (primrec_add₂ (primrec_listLenChar.comp hcw) (Nat.Primrec.const 1))
  have hcat : Nat.Primrec (fun w => bExistsFn
      (fun w'' => matchesBCatGLookup
        (Nat.pair w''.unpair.2.unpair.1 (Nat.pair w''.unpair.1 w''.unpair.2.unpair.2)))
      (Nat.pair w.unpair.1 (Nat.pair w.unpair.2.unpair.1 w.unpair.2.unpair.2))
      (listLenChar w.unpair.2.unpair.2 + 1)) :=
    ((primrec_bExistsFn hg).comp hcatpack).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have ha : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hc)
  have hb : Nat.Primrec (fun w => w.unpair.2.unpair.1.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp hc)
  have hlk1 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.1.unpair.2.unpair.1 w.unpair.2.unpair.2) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair htable
      (Nat.Primrec.pair (Nat.Primrec.pair ha hcw) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hlk2 : Nat.Primrec (fun w => nthCode w.unpair.1
      (Nat.pair w.unpair.2.unpair.1.unpair.2.unpair.2 w.unpair.2.unpair.2) 0) :=
    (primrec_nthCode.comp (Nat.Primrec.pair htable
      (Nat.Primrec.pair (Nat.Primrec.pair hb hcw) (Nat.Primrec.const 0)))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hcap := primrec_mul₂ hlk1 hlk2
  refine (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hcat
        (primrec_selectFn h34 hcap (Nat.Primrec.const 0))))).of_eq fun w => ?_
  show _ = matchesBCharBody (fun p' => nthCode w.unpair.1 p' 0) w.unpair.2.unpair.1 w.unpair.2.unpair.2
  rw [matchesBCharBody_eq]
  match tag : w.unpair.2.unpair.1.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | 2 =>
    have h01' : (1 - 2 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 2 : ℕ) = 0 := rfl
    have h23' : (3 - 2 : ℕ) = 1 := rfl
    simp only [h01', h23', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
    apply eq_of_le_one_iff_one (bExistsFn_le_one _ _ _) (bExistsFn_le_one _ _ _)
    rw [bExistsFn_eq_one_iff, bExistsFn_eq_one_iff]
    refine exists_congr fun i => and_congr_right fun _ => ?_
    simp only [matchesBCatGLookup, unpair_pair_fst, unpair_pair_snd]
  | 3 =>
    have h01' : (1 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - 3 : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - 3 : ℕ) = 0 := rfl
    have h34' : (4 - 3 : ℕ) = 1 := rfl
    simp only [h01', h34', isOne_zero, isOne_one, selectFn_zero, selectFn_one,
      mulBit]
  | t + 4 =>
    have h01' : (1 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h23' : (3 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h34' : (4 - (t + 4) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', h23', h34', isOne_zero, selectFn_zero]

end Domain.Recursive
