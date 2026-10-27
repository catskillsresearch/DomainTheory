module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

/-- Pack `(remK, posC, negC, uCode)` into a single state code. -/
def packState (remK posC negC uCode : ℕ) : ℕ := Nat.pair remK (Nat.pair posC (Nat.pair negC uCode))

def stateCode (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.2

def stateNeg (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.1

def statePos (s : ℕ) : ℕ := s.unpair.2.unpair.1

def stateRem (s : ℕ) : ℕ := s.unpair.1

@[simp] theorem stateRem_packState (a b c d : ℕ) : stateRem (packState a b c d) = a := by
  unfold stateRem packState; simp only [unpair_pair_fst]

@[simp] theorem statePos_packState (a b c d : ℕ) : statePos (packState a b c d) = b := by
  unfold statePos packState; simp only [unpair_pair_fst, unpair_pair_snd]

@[simp] theorem stateNeg_packState (a b c d : ℕ) : stateNeg (packState a b c d) = c := by
  unfold stateNeg packState; simp only [unpair_pair_fst, unpair_pair_snd]

@[simp] theorem stateCode_packState (a b c d : ℕ) : stateCode (packState a b c d) = d := by
  unfold stateCode packState; simp only [unpair_pair_snd]

/-- The initial state at depth `0`: no constraints yet (`posC = negC = 0`, the empty-list code),
`U`-side code is `U.master`'s (`UmasterIdx`), and the unconsumed bit-source is the whole of `k`. -/
def atomBase (k : ℕ) : ℕ := packState k 0 0 UmasterIdx

/-- **The bit-sequence associated to a bit-source `k`**: `deltaOf k i = true` iff bit `i` of `k`
(read low-bit-first, matching `atomStep`'s `remK % 2`/`remK / 2` peeling) is `1`. -/
def deltaOf (k : ℕ) : ℕ → Bool := fun i => decide ((k / 2 ^ i) % 2 = 1)

/-- **`unionUX n m` codes `UX n ∪ UX m`.** Canonicalizes both inputs first (mirroring `Uinter`),
then concatenates; the result is always a genuine `U`-neighbourhood since a union of two such is
again presentable, non-empty, and `⊆ [0,1)`. -/
def unionUX (n m : ℕ) : ℕ := Domain.Recursive.appendCode (canonCode n) (canonCode m)

/-- Extract the packed `(remK, posC, negC, uCode)` state from `w = pair k (pair y state)`. -/
def wState (w : ℕ) : ℕ := w.unpair.2.unpair.2

/-- Extract the current depth `y` from a packed step-input `w = pair k (pair y state)`. -/
def wY (w : ℕ) : ℕ := w.unpair.2.unpair.1

/-- **The per-step state transition.** `datomDec` should be `DAtom_recDecidable (P0 P)`'s extracted
decider (`datomDec (pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅`);
kept abstract here so `Nat.Primrec`-ness can be proved once and reused. `bit := remK % 2`, then:
`posC' := pair y posC + 1` / `negC' := pair y negC + 1` are the candidate accumulators with the
current index `y` prepended; `emptyI`/`emptyJ` decide whether the "+"/"-"-refinements are already
`D`-side empty; the new `U`-code either stays `0` (junk, `D`-side empty), is carried over unchanged
(the refinement equals the old atom outright), or is `splitULeft`/`splitURight` of the old code
(a genuine split). -/
def atomStep (datomDec : ℕ → ℕ) (w : ℕ) : ℕ :=
  let y := wY w
  let s := wState w
  let bit := stateRem s % 2
  let posC' := Nat.pair y (statePos s) + 1
  let negC' := Nat.pair y (stateNeg s) + 1
  let emptyI := datomDec (Nat.pair posC' (stateNeg s))
  let emptyJ := datomDec (Nat.pair (statePos s) negC')
  packState (stateRem s / 2) (selectFn bit posC' (statePos s)) (selectFn bit (stateNeg s) negC')
    (selectFn bit
      (selectFn emptyI 0 (selectFn emptyJ (stateCode s) (splitULeft (stateCode s))))
      (selectFn emptyJ 0 (selectFn emptyI (stateCode s) (splitURight (stateCode s)))))

theorem deltaOf_eq_testBit (k i : ℕ) : deltaOf k i = k.testBit i :=
  Nat.testBit_eq_decide_div_mod_eq.symm

/-- Adding `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_add_two_pow_of_lt {n : ℕ} (m : ℕ) {i : ℕ} (hi : i < n) :
    deltaOf (m + 2 ^ n) i = deltaOf m i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_gt hi]

/-- Adding `2ⁿ` to an `m < 2ⁿ` sets exactly bit `n` (no carry beyond it). -/
theorem deltaOf_two_pow_add_self {n m : ℕ} (hm : m < 2 ^ n) : deltaOf (m + 2 ^ n) n = true := by
  rw [deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
  rfl

/-- **`δ`'s length-`n` bit-encoding**: the natural number `< 2 ^ n` agreeing with `δ` on every bit
below `n`. -/
def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => encodeBits δ n + (if δ n then 2 ^ n else 0)

theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | (n + 1) => by
      have ih := encodeBits_lt δ n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with h | h <;> simp [h] <;> omega

theorem deltaOf_encodeBits (δ : ℕ → Bool) : ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, ite_eq_left rfl, deltaOf_add_two_pow_of_lt _ hi']
        exact ih i hi'
      · rw [h, ite_eq_right (by simp), Nat.add_zero]
        exact ih i hi'
    · rw [hi']
      rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, ite_eq_left rfl]
        exact deltaOf_two_pow_add_self (encodeBits_lt δ n)
      · rw [h, ite_eq_right (by simp), Nat.add_zero, deltaOf_eq_testBit,
          Nat.testBit_lt_two_pow (encodeBits_lt δ n)]

namespace AtomCode

theorem primrec_atomBase : Nat.Primrec atomBase :=
  ((Nat.Primrec.id).pair ((Nat.Primrec.const 0).pair
    ((Nat.Primrec.const 0).pair (Nat.Primrec.const UmasterIdx)))).of_eq fun k => by
    unfold atomBase packState; simp only [id_eq]

theorem primrec_stateCode : Nat.Primrec stateCode :=
  Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_stateNeg : Nat.Primrec stateNeg :=
  Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_statePos : Nat.Primrec statePos := Nat.Primrec.left.comp Nat.Primrec.right

theorem primrec_stateRem : Nat.Primrec stateRem := Nat.Primrec.left

theorem primrec_unionUX : Nat.Primrec (fun t : ℕ => unionUX t.unpair.1 t.unpair.2) := by
  unfold unionUX
  exact (Domain.Recursive.primrec_appendCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_wState : Nat.Primrec wState := Nat.Primrec.right.comp Nat.Primrec.right

theorem primrec_wY : Nat.Primrec wY := Nat.Primrec.left.comp Nat.Primrec.right

theorem primrec_atomStep {datomDec : ℕ → ℕ} (hd : Nat.Primrec datomDec) :
    Nat.Primrec (atomStep datomDec) := by
  have hy : Nat.Primrec wY := primrec_wY
  have hs : Nat.Primrec wState := primrec_wState
  have hrem : Nat.Primrec (fun w => stateRem (wState w)) := primrec_stateRem.comp hs
  have hpos : Nat.Primrec (fun w => statePos (wState w)) := primrec_statePos.comp hs
  have hneg : Nat.Primrec (fun w => stateNeg (wState w)) := primrec_stateNeg.comp hs
  have hcode : Nat.Primrec (fun w => stateCode (wState w)) := primrec_stateCode.comp hs
  have hbit : Nat.Primrec (fun w => stateRem (wState w) % 2) := primrec_mod2.comp hrem
  have hposC' : Nat.Primrec (fun w => Nat.pair (wY w) (statePos (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hpos)
  have hnegC' : Nat.Primrec (fun w => Nat.pair (wY w) (stateNeg (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hneg)
  have hemptyI : Nat.Primrec (fun w => datomDec (Nat.pair
      (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w)))) :=
    hd.comp (hposC'.pair hneg)
  have hemptyJ : Nat.Primrec (fun w => datomDec (Nat.pair (statePos (wState w))
      (Nat.pair (wY w) (stateNeg (wState w)) + 1))) :=
    hd.comp (hpos.pair hnegC')
  have hsplitL : Nat.Primrec (fun w => splitULeft (stateCode (wState w))) :=
    primrec_splitULeft.comp hcode
  have hsplitR : Nat.Primrec (fun w => splitURight (stateCode (wState w))) :=
    primrec_splitURight.comp hcode
  have hcodeBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
        0 (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) (stateCode (wState w)) (splitULeft (stateCode (wState w)))))
      (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) 0
        (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
          (stateCode (wState w)) (splitURight (stateCode (wState w)))))) :=
    primrec_selectFn hbit
      (primrec_selectFn hemptyI (Nat.Primrec.const 0) (primrec_selectFn hemptyJ hcode hsplitL))
      (primrec_selectFn hemptyJ (Nat.Primrec.const 0) (primrec_selectFn hemptyI hcode hsplitR))
  have hrem' : Nat.Primrec (fun w => stateRem (wState w) / 2) := primrec_div2.comp hrem
  have hposBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (Nat.pair (wY w) (statePos (wState w)) + 1) (statePos (wState w))) :=
    primrec_selectFn hbit hposC' hpos
  have hnegBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (stateNeg (wState w)) (Nat.pair (wY w) (stateNeg (wState w)) + 1)) :=
    primrec_selectFn hbit hneg hnegC'
  exact (hrem'.pair (hposBranch.pair (hnegBranch.pair hcodeBranch))).of_eq fun w => by
    unfold atomStep packState
    simp only []

end AtomCode

end DomainTheory.NeighbourhoodSystems
