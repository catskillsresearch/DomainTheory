module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

def VmasterIdx : ℕ := Nat.pair 0 1

def lowAnd (x y : ℕ) : ℕ := x % 2 * (y % 2)

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem lowAnd : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.lowAnd t.unpair.1 t.unpair.2) :=
  (primrec_mul₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right)).of_eq
    fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

def landStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowAnd s.unpair.1.unpair.1 s.unpair.1.unpair.2))

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem landStep : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.landStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => _root_.DomainTheory.NeighbourhoodSystems.lowAnd s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec.lowAnd.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

end primrec
namespace levelSet
open Domain.Recursive NeighborhoodSystem

theorem inj_of_lt {k a b : ℕ} (ha : a < 2 ^ (2 ^ k)) (hb : b < 2 ^ (2 ^ k))
    (h : levelSet k a = levelSet k b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro ℓ
  by_cases hℓ : ℓ < 2 ^ k
  · have hiff := Set.ext_iff.mp h ℓ
    simp only [mem_levelSet, Nat.mod_eq_of_lt hℓ] at hiff
    cases ha' : a.testBit ℓ <;> cases hb' : b.testBit ℓ <;> simp_all
  · have hpow : (2:ℕ) ^ (2 ^ k) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hℓ)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

end levelSet
open Domain.Recursive NeighborhoodSystem

theorem lowAnd_eq_mod (x y : ℕ) : lowAnd x y = (x &&& y) % 2 := by
  have key : ((x &&& y) % 2 = 1) ↔ (x % 2 = 1 ∧ y % 2 = 1) := by
    have hb := Nat.testBit_and x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_and]
  unfold lowAnd
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · exact (key.mpr ⟨hx, hy⟩).symm

theorem land_low_rec (x y : ℕ) : x &&& y = 2 * (x / 2 &&& y / 2) + lowAnd x y := by
  have hdiv : (x &&& y) / 2 = x / 2 &&& y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_and, Nat.testBit_and, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowAnd_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x &&& y) 2]
  rw [hdiv, hmod]

theorem landStep_iter_spec (a b : ℕ) : ∀ k,
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k &&& b / 2 ^ k) = a &&& b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have p11 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold landStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (landStep (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowAnd (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (landStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold landStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, land_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

theorem mod_eq_sub_of_le_of_lt_two_mul {j s : ℕ} (h1 : s ≤ j) (h2 : j < 2 * s) :
    j % s = j - s := by
  have heq : j = (j - s) + s := by omega
  calc j % s = ((j - s) + s) % s := by rw [← heq]
    _ = (j - s) % s := Nat.add_mod_right _ _
    _ = j - s := Nat.mod_eq_of_lt (by omega)

def myDivPow2 (m ℓ : ℕ) : ℕ := Nat.unpaired (fun z n => n.rec z (fun _ ih => ih / 2)) (Nat.pair m ℓ)

def myModPow2 (m s : ℕ) : ℕ := m - myDivPow2 m s * 2 ^ s

def myTestBit (m ℓ : ℕ) : ℕ := myDivPow2 m ℓ % 2

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem myDivPow2 : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myDivPow2 t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec Nat.Primrec.id hg).of_eq fun t => ?_
  unfold _root_.DomainTheory.NeighbourhoodSystems.myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]

theorem myModPow2 : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myModPow2 t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  have hdiv : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myDivPow2 t.unpair.1 t.unpair.2) := primrec.myDivPow2
  exact (primrec_sub₂ Nat.Primrec.left (primrec_mul₂ hdiv hpow)).of_eq fun t => rfl

theorem myTestBit : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myTestBit t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp primrec.myDivPow2).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

theorem myDivPow2_eq (m ℓ : ℕ) : myDivPow2 m ℓ = m / 2 ^ ℓ := by
  unfold myDivPow2
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    show (ℓ.rec m (fun _ ih => ih / 2)) / 2 = m / 2 ^ (ℓ + 1)
    rw [ih, Nat.div_div_eq_div_mul, ← pow_succ]

namespace myModPow2
open Domain.Recursive NeighborhoodSystem

theorem eq (m s : ℕ) : myModPow2 m s = m % 2 ^ s := by
  unfold myModPow2
  rw [myDivPow2_eq]
  have h : m / 2 ^ s * 2 ^ s + m % 2 ^ s = m := by
    rw [mul_comm]; exact Nat.div_add_mod m (2 ^ s)
  omega

end myModPow2
namespace myTestBit
open Domain.Recursive NeighborhoodSystem

theorem eq_one_iff (m ℓ : ℕ) : myTestBit m ℓ = 1 ↔ m.testBit ℓ = true := by
  unfold myTestBit
  rw [myDivPow2_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

end myTestBit
namespace myModPow2
open Domain.Recursive NeighborhoodSystem

theorem lt (m s : ℕ) : myModPow2 m s < 2 ^ s := by
  rw [myModPow2.eq]; exact Nat.mod_lt m (Nat.two_pow_pos s)

end myModPow2
namespace levelSet
open Domain.Recursive NeighborhoodSystem

theorem myModPow2 (k x : ℕ) : levelSet k (_root_.DomainTheory.NeighbourhoodSystems.myModPow2 x (2 ^ k)) = levelSet k x := by
  ext n
  simp only [mem_levelSet, myModPow2.eq, Nat.testBit_mod_two_pow]
  have : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  simp [this]

end levelSet
open Domain.Recursive NeighborhoodSystem

def myLand (a b : ℕ) : ℕ :=
  (landStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem myLand : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myLand t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.landStep w.unpair.2.unpair.2) :=
    primrec.landStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

end primrec
open Domain.Recursive NeighborhoodSystem

theorem myLand_eq_land (a b : ℕ) : myLand a b = a &&& b := by
  unfold myLand
  obtain ⟨_, _, _, hAcc⟩ := landStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

def levelSetNonemptyBody (t : ℕ) : ℕ := myTestBit t.unpair.2 t.unpair.1

def myLevelSetNonempty (k m : ℕ) : ℕ := bExistsFn levelSetNonemptyBody m (2 ^ k)

def canonIdx (c : ℕ) : ℕ :=
  selectFn (myLevelSetNonempty c.unpair.1 c.unpair.2) c (Nat.pair 0 1)

namespace myLevelSetNonempty
open Domain.Recursive NeighborhoodSystem

theorem le_one (k m : ℕ) : myLevelSetNonempty k m ≤ 1 :=
  bExistsFn_le_one _ _ _

theorem eq_one_iff (k m : ℕ) :
    myLevelSetNonempty k m = 1 ↔ (levelSet k m).Nonempty := by
  unfold myLevelSetNonempty
  rw [bExistsFn_eq_one_iff, levelSet.nonempty_iff]
  simp only [levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd, myTestBit.eq_one_iff]

end myLevelSetNonempty
namespace canonIdx
open Domain.Recursive NeighborhoodSystem

theorem eq_master_of_empty {c : ℕ} (h : levelSet c.unpair.1 c.unpair.2 = ∅) :
    canonIdx c = Nat.pair 0 1 := by
  unfold canonIdx
  have hle := myLevelSetNonempty.le_one c.unpair.1 c.unpair.2
  have hne1 : myLevelSetNonempty c.unpair.1 c.unpair.2 ≠ 1 := fun heq =>
    ((myLevelSetNonempty.eq_one_iff _ _).mp heq).ne_empty h
  have h0 : myLevelSetNonempty c.unpair.1 c.unpair.2 = 0 := by omega
  rw [h0, selectFn_zero]

theorem eq_self_of_nonempty {c : ℕ} (h : (levelSet c.unpair.1 c.unpair.2).Nonempty) :
    canonIdx c = c := by
  unfold canonIdx
  rw [(myLevelSetNonempty.eq_one_iff _ _).mpr h, selectFn_one]

end canonIdx
namespace levelSet
open Domain.Recursive NeighborhoodSystem

theorem canonIdx_nonempty (c : ℕ) :
    (levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2).Nonempty := by
  by_cases h : (levelSet c.unpair.1 c.unpair.2).Nonempty
  · rwa [canonIdx.eq_self_of_nonempty h]
  · rw [canonIdx.eq_master_of_empty (Set.not_nonempty_iff_eq_empty.mp h), unpair_pair_fst,
      unpair_pair_snd, levelSet.zero_one]
    exact Set.univ_nonempty

end levelSet
namespace canonIdx
open Domain.Recursive NeighborhoodSystem

theorem idempotent (c : ℕ) : canonIdx (canonIdx c) = canonIdx c :=
  canonIdx.eq_self_of_nonempty (levelSet.canonIdx_nonempty c)

end canonIdx
namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem levelSetNonemptyBody : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.levelSetNonemptyBody :=
  (primrec.myTestBit.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd]

theorem myLevelSetNonempty :
    Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myLevelSetNonempty t.unpair.1 t.unpair.2) := by
  have hbe : Nat.Primrec (fun t : ℕ => bExistsFn _root_.DomainTheory.NeighbourhoodSystems.levelSetNonemptyBody t.unpair.1 t.unpair.2) :=
    primrec_bExistsFn primrec.levelSetNonemptyBody
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  exact (hbe.comp (Nat.Primrec.right.pair hpow)).of_eq fun t => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.myLevelSetNonempty, unpair_pair_fst, unpair_pair_snd]

theorem canonIdx : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.canonIdx := by
  have hne : Nat.Primrec (fun c => _root_.DomainTheory.NeighbourhoodSystems.myLevelSetNonempty c.unpair.1 c.unpair.2) :=
    primrec.myLevelSetNonempty
  exact (primrec_selectFn hne primrec_id (Nat.Primrec.const (Nat.pair 0 1))).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

def VX (c : ℕ) : Set ℕ := levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2

theorem VX_VmasterIdx : VX VmasterIdx = V.master := by
  have hne : (levelSet (Nat.pair 0 1 : ℕ).unpair.1 (Nat.pair 0 1 : ℕ).unpair.2).Nonempty := by
    rw [unpair_pair_fst, unpair_pair_snd, levelSet.zero_one]; exact Set.univ_nonempty
  unfold VX VmasterIdx
  rw [canonIdx.eq_self_of_nonempty hne, unpair_pair_fst, unpair_pair_snd, levelSet.zero_one]
  rfl

theorem V.surj_VX : ∀ {Y : Set ℕ}, V.mem Y → ∃ n, VX n = Y := by
  rintro Y ⟨k, m, rfl, hne⟩
  refine ⟨Nat.pair k m, ?_⟩
  have hne' : (levelSet (Nat.pair k m).unpair.1 (Nat.pair k m).unpair.2).Nonempty := by
    rwa [unpair_pair_fst, unpair_pair_snd]
  unfold VX
  rw [canonIdx.eq_self_of_nonempty hne', unpair_pair_fst, unpair_pair_snd]

theorem VX_nonempty (c : ℕ) : (VX c).Nonempty := levelSet.canonIdx_nonempty c

theorem V.mem_VX (c : ℕ) : V.mem (VX c) :=
  ⟨(canonIdx c).unpair.1, (canonIdx c).unpair.2, rfl, levelSet.canonIdx_nonempty c⟩

theorem VX_canonIdx (c : ℕ) : VX (canonIdx c) = VX c := by unfold VX; rw [canonIdx.idempotent]

end DomainTheory.NeighbourhoodSystems
