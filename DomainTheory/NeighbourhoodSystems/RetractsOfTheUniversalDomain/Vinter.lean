module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- One computable upsampling step: re-express a level-`k` mask at level `k + 1` by duplicating its
low `2^k` bits into a second copy shifted up by `2^k` positions. -/
def myUpsampleStep (k m : ℕ) : ℕ :=
  2 ^ (2 ^ k) * myModPow2 m (2 ^ k) + myModPow2 m (2 ^ k)

/-- Joint (level, mask) iteration state for `myUpsample`: `pair level mask`. -/
def myUpsampleJointStep (s : ℕ) : ℕ :=
  Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2)

namespace myUpsampleJointStep
open Domain.Recursive NeighborhoodSystem

/-- Unfolding equation for `myUpsampleJointStep`, stated so `rw` fires on a single (outer)
occurrence rather than `unfold`ing every nested occurrence (in particular, the ones hidden inside
an already-iterated `myUpsampleJointStep^[d]` term). -/
theorem eq (s : ℕ) :
    myUpsampleJointStep s = Nat.pair (s.unpair.1 + 1) (myUpsampleStep s.unpair.1 s.unpair.2) := rfl

/-- Iterate `myUpsampleJointStep` `d` times from `pair k m`, and read off the level after `d`
steps and the resulting mask. -/
theorem iter_level (k m d : ℕ) :
    (myUpsampleJointStep^[d] (Nat.pair k m)).unpair.1 = k + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep.eq, unpair_pair_fst, ih]
    omega

end myUpsampleJointStep
namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **The key correctness lemma for `myUpsampleStep`**: it realizes `Exercise812.lean`'s
mathematical `upsample` at the `levelSet` level, one step at a time. -/
theorem myUpsampleStep (k m : ℕ) :
    levelSet (k + 1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsampleStep k m) = levelSet k m := by
  ext n
  simp only [mem_levelSet]
  have hlt : _root_.DomainTheory.NeighbourhoodSystems.myModPow2 m (2 ^ k) < 2 ^ (2 ^ k) := myModPow2.lt m (2 ^ k)
  have hstep : _root_.DomainTheory.NeighbourhoodSystems.myUpsampleStep k m
      = 2 ^ (2 ^ k) * _root_.DomainTheory.NeighbourhoodSystems.myModPow2 m (2 ^ k) + _root_.DomainTheory.NeighbourhoodSystems.myModPow2 m (2 ^ k) := rfl
  rw [hstep, Nat.testBit_two_pow_mul_add _ hlt]
  have hmm : n % 2 ^ k = n % 2 ^ (k + 1) % 2 ^ k :=
    (Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (Nat.le_succ k))).symm
  have hjlt : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt n (Nat.two_pow_pos (k + 1))
  have h2 : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  by_cases hcase : n % 2 ^ (k + 1) < 2 ^ k
  · rw [ite_eq_left hcase, myModPow2.eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hcase,
      Bool.true_and, hmm, Nat.mod_eq_of_lt hcase]
  · have hge : 2 ^ k ≤ n % 2 ^ (k + 1) := Nat.le_of_not_lt hcase
    have hsub : n % 2 ^ (k + 1) - 2 ^ k < 2 ^ k := by omega
    rw [ite_eq_right hcase, myModPow2.eq, Nat.testBit_mod_two_pow, decide_eq_true_iff.mpr hsub,
      Bool.true_and, hmm, mod_eq_sub_of_le_of_lt_two_mul hge (h2 ▸ hjlt)]

end levelSet
namespace myUpsampleJointStep
open Domain.Recursive NeighborhoodSystem

theorem iter_levelSet (k m d : ℕ) :
    levelSet (k + d) ((myUpsampleJointStep^[d] (Nat.pair k m)).unpair.2) = levelSet k m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep.eq, unpair_pair_snd,
      myUpsampleJointStep.iter_level, show k + (d + 1) = (k + d) + 1 from by omega,
      levelSet.myUpsampleStep, ih]

end myUpsampleJointStep
namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem myUpsampleStep : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myUpsampleStep t.unpair.1 t.unpair.2) := by
  have hs : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.1) := primrec_two_pow Nat.Primrec.left
  have hm' : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myModPow2 t.unpair.2 (2 ^ t.unpair.1)) :=
    (primrec.myModPow2.comp (Nat.Primrec.right.pair hs)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2s : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ (2 ^ t.unpair.1)) := primrec_two_pow hs
  exact (primrec_add₂ (primrec_mul₂ h2s hm') hm').of_eq fun t => rfl

theorem myUpsampleJointStep : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.myUpsampleJointStep := by
  have hstep : Nat.Primrec (fun s : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsampleStep s.unpair.1 s.unpair.2) :=
    primrec.myUpsampleStep
  exact ((Nat.Primrec.succ.comp Nat.Primrec.left).pair hstep).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **`myUpsample k k' m`**: the computable re-expression of a level-`k` mask `m` at level
`k' ≥ k`, agreeing with `Exercise812.lean`'s (non-computable) `upsample` at the `levelSet` level
(`levelSet.myUpsample`), and always *bounded* (`myUpsample_lt`) — the final `myModPow2` truncation
is a no-op mathematically (`levelSet.myModPow2`) but is essential to guarantee boundedness in the
degenerate `k = k'` case, where the raw iteration runs zero steps and would otherwise return `m`
unchanged (junk bits included). Undefined behaviour (returns junk) when `k' < k`. -/
def myUpsample (k k' m : ℕ) : ℕ :=
  myModPow2 ((myUpsampleJointStep^[k' - k] (Nat.pair k m)).unpair.2) (2 ^ k')

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **`myUpsample` realizes `upsample` at the `levelSet` level.** -/
theorem myUpsample {k k' : ℕ} (hk : k ≤ k') (m : ℕ) :
    levelSet k' (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k k' m) = levelSet k m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.myUpsample
  rw [levelSet.myModPow2]
  have := myUpsampleJointStep.iter_levelSet k m (k' - k)
  rwa [show k + (k' - k) = k' from by omega] at this

/-- **Computable version of `levelSet.inter`.** -/
theorem myInter (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∩ levelSet k2 m2
      = levelSet (max k1 k2) (myLand (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet.inter_same_level, myLand_eq_land]

end levelSet
namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem myUpsample :
    Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myUpsample t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hstep : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.myUpsampleJointStep w.unpair.2.unpair.2) :=
    primrec.myUpsampleJointStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec primrec_id hstep
  have hz : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1 - t.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hmodpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2.unpair.1) :=
    primrec_two_pow (Nat.Primrec.left.comp Nat.Primrec.right)
  refine (primrec.myModPow2.comp ((Nat.Primrec.right.comp (hprec.comp (hz.pair hn))).pair
    hmodpow)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  unfold _root_.DomainTheory.NeighbourhoodSystems.myUpsample
  rw [rec_const_iterate]

end primrec
open Domain.Recursive NeighborhoodSystem

/-- The **raw** `(level, mask)` code for `VX n ∩ VX m`, before re-canonicalization: upsample both
`canonIdx`-normalized masks to the common level `max k₁ k₂` and take `myLand`. -/
def VinterRaw (n m : ℕ) : ℕ :=
  Nat.pair (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
    (myLand
      (myUpsample (canonIdx n).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx n).unpair.2)
      (myUpsample (canonIdx m).unpair.1 (max (canonIdx n).unpair.1 (canonIdx m).unpair.1)
        (canonIdx m).unpair.2))

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **`VinterRaw` realizes `VX n ∩ VX m`** at the `levelSet` level (unconditionally — `V`'s
consistency is genuinely automatic, mirroring `PN`). -/
theorem VinterRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VinterRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VinterRaw n m).unpair.2 = VX n ∩ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VinterRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myInter (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem VinterRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VinterRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1) := primrec.canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2) := primrec.canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2) :=
    (primrec.myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
      (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2) :=
    (primrec.myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hland : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myLand
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec.myLand.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hland).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- The intersection index: `canonIdx` of the raw intersection code `VinterRaw`. -/
def Vinter (n m : ℕ) : ℕ := canonIdx (VinterRaw n m)

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem Vinter : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vinter t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VinterRaw).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition reduces to non-emptiness.** -/
theorem Vcons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, VX k ⊆ VX n ∩ VX m) ↔ (VX n ∩ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (VX_nonempty k).mono hk
  · intro hne
    rw [← levelSet.VinterRaw] at hne
    have hVmem : V.mem (VX n ∩ VX m) := by
      rw [← levelSet.VinterRaw]
      exact ⟨(VinterRaw n m).unpair.1, (VinterRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V.surj_VX hVmem
    exact ⟨k, by rw [hk]⟩

theorem Vinter_spec {n m : ℕ} (h : ∃ k, VX k ⊆ VX n ∩ VX m) : VX (Vinter n m) = VX n ∩ VX m := by
  have hne : (levelSet (VinterRaw n m).unpair.1 (VinterRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VinterRaw]; exact (Vcons_iff_nonempty_inter n m).mp h
  unfold Vinter
  rw [VX_canonIdx]
  show levelSet (canonIdx (VinterRaw n m)).unpair.1 (canonIdx (VinterRaw n m)).unpair.2 = VX n ∩ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VinterRaw]

/-- **`myUpsample` is always bounded** by `2 ^ (2 ^ k')`, regardless of whether a genuine
upsampling step occurs. -/
theorem myUpsample_lt (k k' m : ℕ) : myUpsample k k' m < 2 ^ (2 ^ k') := myModPow2.lt _ _

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **`levelSet` equality reduces to `myUpsample` equality** at the common level `max k₁ k₂`: this
is the injectivity criterion (`levelSet.inj_of_lt`) driving Scott's relation 7.1(i) decider. -/
theorem eq_iff_myUpsample_eq (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 = levelSet k2 m2 ↔
      _root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1 = _root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2 := by
  constructor
  · intro h
    exact levelSet.inj_of_lt (myUpsample_lt _ _ _) (myUpsample_lt _ _ _)
      (by rw [levelSet.myUpsample (Nat.le_max_left k1 k2),
        levelSet.myUpsample (Nat.le_max_right k1 k2), h])
  · intro h
    rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
      ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2, h]

end levelSet
open Domain.Recursive NeighborhoodSystem

/-- **7.1(ii) for `V`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`Vcons_iff_nonempty_inter` and `myLevelSetNonempty`. -/
theorem V.cons_computable : RecDecidable₂ (fun n m => ∃ k, VX k ⊆ VX n ∩ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2) := primrec.VinterRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec.myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty.le_one (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vcons_iff_nonempty_inter, ← levelSet.VinterRaw,
      myLevelSetNonempty.eq_one_iff]

/-- **7.1(i) for `V`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable, reduced to `myUpsample` equality
of the raw intersection code against `X_k`'s own code (`levelSet.eq_iff_myUpsample_eq`). -/
theorem V.interEq_computable : RecDecidable₃ (fun n m k => VX n ∩ VX m = VX k) := by
  unfold RecDecidable₃
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec.VinterRaw.comp (Nat.Primrec.left.pair
      (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hvrK : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hvr
  have hvrM : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hvr
  have hck : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2.unpair.2) :=
    primrec.canonIdx.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hckK : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    Nat.Primrec.left.comp hck
  have hckM : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    Nat.Primrec.right.comp hck
  have hkJ : Nat.Primrec (fun t : ℕ =>
      max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    primrec_max hvrK hckK
  have hLHS : Nat.Primrec (fun t : ℕ => myUpsample (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    (primrec.myUpsample.comp (hvrK.pair (hkJ.pair hvrM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2.unpair.2).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    (primrec.myUpsample.comp (hckK.pair (hkJ.pair hckM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (RecDecidable.natEq hLHS hRHS)
  dsimp only
  rw [← levelSet.VinterRaw, ← levelSet.eq_iff_myUpsample_eq]
  rfl

/-- **Exercise 8.12(b).** `V` (Exercise 8.12(a)) has a genuine `ComputablePresentation`. -/
def VComputablePresentation : ComputablePresentation V where
  X := VX
  mem_X := V.mem_VX
  surj := V.surj_VX
  interEq_computable := V.interEq_computable
  cons_computable := V.cons_computable
  inter := Vinter
  inter_primrec := primrec.Vinter
  inter_spec := Vinter_spec
  masterIdx := VmasterIdx
  masterIdx_spec := VX_VmasterIdx

/-- **Exercise 8.12(b) (Scott 1981, PRG-19).** `V` is effectively given. -/
theorem V.isEffectivelyGiven : V.IsEffectivelyGiven := ⟨VComputablePresentation⟩

end DomainTheory.NeighbourhoodSystems
