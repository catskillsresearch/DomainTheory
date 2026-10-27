module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DiagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.D_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeUPresentation

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
section
open NeighborhoodSystem
variable {α : Type*}

/- concordance: source L4943 THEOREM 8.8 universality of U -/
/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19, Lecture VIII).** `𝒰` is universal: every *countable*
neighbourhood system `D` embeds, up to isomorphism, as a subsystem of `𝒰`.

The enumeration `e` is built from any surjection `f : ℕ → {S // D.mem S}` (`exists_surjective_nat`,
using `Countable`/`Nonempty` — the only place `Classical.choice` enters, since neither hypothesis is
data), shifted by one and patched at `0` to enforce Scott's convention `X₀ = Δ`. Everything else —
`idxSet`'s "separated" reindexing, the `Yidx`/transfer apparatus of `Theorem88.lean`, and the
`DprimeU`/`domainIso` machinery above — is then assembled directly. -/
theorem theorem_8_8_a.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] :
    ∃ D' : NeighborhoodSystem ℚ, (D ≅ᴰ D') ∧ (D' ◁ U) := by
  have : Nonempty {S : Set α // D.mem S} := ⟨⟨D.master, D.master_mem⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat {S : Set α // D.mem S}
  set e : ℕ → Set α := fun n => if n = 0 then D.master else (f (n - 1)).1 with hedef
  have he0 : e 0 = D.master := ite_eq_left rfl
  have hen : ∀ n, e (n + 1) = (f n).1 := by
    intro n
    show (if n + 1 = 0 then D.master else (f (n + 1 - 1)).1) = (f n).1
    rw [ite_eq_right (Nat.succ_ne_zero n), Nat.succ_sub_one]
  have hcover : ∀ S, D.mem S ↔ ∃ n, S = e n := by
    intro S
    constructor
    · intro hS
      obtain ⟨k, hk⟩ := hf ⟨S, hS⟩
      exact ⟨k + 1, by rw [hen k]; exact (congrArg Subtype.val hk).symm⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => rw [he0]; exact D.master_mem
      | succ n => rw [hen n]; exact (f n).2
  exact ⟨DprimeU D e hcover he0, isomorphic_DprimeU D e hcover he0, DprimeU_subsystem D e hcover he0⟩

/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19).** Scott's wording:
"The system `𝒰` is universal in the sense that, for every countable neighbourhood
system `𝒟`, we have `𝒟 ⊴ 𝒰`." This packages `theorem_8_8_a` as that relation. -/
theorem theorem_8_8.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

end









end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem88d
open NeighborhoodSystem Domain.Recursive

section
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

private def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => encodeBits δ n + (if δ n then 2 ^ n else 0)
end

end DomainTheory.NeighbourhoodSystems.Theorem88d
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Per-step `D`-side correctness.** The accumulated `(pos, neg)` code pair at depth `n`, for
bit-source `k`, tracks exactly the same atom as `genAtom (idxSet (e P)) Set.univ (deltaOf k) n`. -/
theorem genAtom_atomUCode (k : ℕ) :
    ∀ n, genAtom (idxSet (e P)) Set.univ (deltaOf k) n
      = DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
  intro n
  induction n with
  | zero =>
    simp [genAtom, atomUPos, atomUNeg, atomUCodeState, atomBase, DAtom, decodeList_zero, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hbit1 : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp hδ
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit1, selectFn_one, selectFn_one,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos, Set.inter_comm]
    · have hbit0 : (k / 2 ^ n) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos ((k / 2 ^ n) % 2) with h | h
        · exact h
        · exact absurd ((deltaOf_eq_true_iff k n).mpr (by omega)) (by simp [hδ])
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit0, selectFn_zero, selectFn_zero,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg, Set.inter_comm]


/-- **`atomUEmpty` reads off `genAtom`'s own emptiness**, via `genAtom_atomUCode`. -/
theorem atomUEmpty_eq_one_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n = ∅ := by
  rw [atomUEmpty_eq_one_iff, ← genAtom_atomUCode]

theorem atomUEmpty_eq_zero_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 0 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n ≠ ∅ := by
  have hle : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
  have h1 := atomUEmpty_eq_one_iff_genAtom P n k
  constructor
  · intro h0 hempty; exact absurd (h1.mpr hempty) (by omega)
  · intro hne; by_contra h0; exact hne (h1.mp (by omega))


theorem genAtom_succ_subset (k n : ℕ) :
    genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) ⊆
      genAtom (idxSet (e P)) Set.univ (deltaOf k) n :=
  Set.inter_subset_left

theorem atomUEmpty_mono {n k : ℕ} (h : atomUEmpty P n k = 1) : atomUEmpty P (n + 1) k = 1 := by
  rw [atomUEmpty_eq_one_iff_genAtom] at h ⊢
  exact Set.subset_eq_empty (genAtom_succ_subset P k n) h

theorem atomUEmpty_zero_of_succ {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) : atomUEmpty P n k = 0 := by
  by_contra hne
  have hle := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  have h1 : atomUEmpty P n k = 1 := by unfold atomUEmpty at hne hle ⊢; omega
  exact absurd (atomUEmpty_mono P h1) (by omega)


/-- **The core `(vii)(1)` result**: at every depth `n`, atoms for bit-sources disagreeing somewhere
below `n` are disjoint on the `U`-side, *provided both are still `D`-side non-empty*. Proved by
induction on `n`, mirroring `atomU_invariant`'s disjointness clause: either the disagreement is
already below `n - 1` (recurse, then shrink both sides via `atomUCode.subset`), or it is exactly at
the last bit (use `atomUCodeState_congr` to identify the shared depth-`(n-1)` ancestor, then
`splitU_disjoint`, since both survive to depth `n` iff that step was a genuine split). -/
theorem atomUCode_disjoint :
    ∀ n k k', atomUEmpty P n k = 0 → atomUEmpty P n k' = 0 → (∃ i < n, deltaOf k i ≠ deltaOf k' i) →
      UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ := by
  intro n
  induction n with
  | zero => intro k k' _ _ ⟨i, hi, _⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k k' hk hk' ⟨i, hi, hne⟩
    by_cases hagree : ∀ j < n, deltaOf k j = deltaOf k' j
    · have hδn : deltaOf k n ≠ deltaOf k' n := by
        intro heq
        apply hne
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact hagree i hi'
        · exact heq
      obtain ⟨hpos, hneg, hcode⟩ := atomUCodeState_congr P hagree
      rw [atomUCode.succ, atomUCode.succ, hpos, hneg, hcode]
      -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
      rcases Bool.eq_false_or_eq_true (deltaOf k n) with h1 | h1
      · -- `deltaOf k n = true`: `k` takes bit `1`, so `deltaOf k' n` must be `false`.
        have hbitk : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp h1
        have h2 : deltaOf k' n = false := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact absurd (h1.trans h2.symm) hδn
          · exact h2
        have hbitk' : (k' / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k' n).mpr hh) (by simp [h2])
        have hkI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_one] at h; exact h
        have hk'J : datomDec P (Nat.pair (atomUPos P n k') (Nat.pair n (atomUNeg P n k') + 1)) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_zero] at h; exact h
        rw [hpos, hneg] at hkI
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkI, hk'J]
        exact splitU_disjoint (atomUCode P n k')
      · -- `deltaOf k n = false`: `k` takes bit `0`, so `deltaOf k' n` must be `true`.
        have hbitk : (k / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [h1])
        have h2 : deltaOf k' n = true := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact h2
          · exact absurd (h1.trans h2.symm) hδn
        have hbitk' : (k' / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k' n).mp h2
        have hkJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_zero] at h; exact h
        have hk'I : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k') + 1) (atomUNeg P n k')) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_one] at h; exact h
        rw [hpos, hneg] at hkJ
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkJ, hk'I]
        exact (Set.inter_comm _ _).trans (splitU_disjoint (atomUCode P n k'))
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hd : UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ :=
        ih k k' (atomUEmpty_zero_of_succ P hk) (atomUEmpty_zero_of_succ P hk') ⟨j, hj, hjne⟩
      exact Set.subset_eq_empty
        (Set.inter_subset_inter (atomUCode.subset P hk) (atomUCode.subset P hk')) hd

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

namespace Theorem88d

private theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | n + 1 => by
      have ih := encodeBits_lt δ n
      have hp := Nat.two_pow_pos n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn <;> simp [hδn] <;> omega

private theorem deltaOf_encodeBits (δ : ℕ → Bool) :
    ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i
  | n + 1, i, hi => by
      have hlt := encodeBits_lt δ n
      show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n + 2 ^ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [deltaOf_add_two_pow_of_lt _ hi']; exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_two_pow_add_self hlt, hδn]
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_eq_testBit, Nat.testBit_lt_two_pow hlt, hδn]

end Theorem88d

theorem exists_atomUEmpty_zero (n : ℕ) : ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  classical
  set δ0 : ℕ → Bool := fun j => decide (n ∈ idxSet (e P) j) with hδ0def
  have hδ0n : δ0 n = true := by
    show decide (n ∈ idxSet (e P) n) = true
    rw [decide_eq_true_iff]; exact self_mem_idxSet (e P) n
  have hstep : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) =
      genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n := by
    show genAtom (idxSet (e P)) Set.univ δ0 n ∩
      (if δ0 n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
    simp [hδ0n]
  have hxn : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n :=
    genAtom_self (idxSet (e P)) Set.univ (Set.mem_univ n) n
  have hmem : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n :=
    ⟨hxn, self_mem_idxSet (e P) n⟩
  have hAne : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) ≠ ∅ := by
    rw [hstep]; exact Set.Nonempty.ne_empty ⟨n, hmem⟩
  set m0 := Theorem88d.encodeBits δ0 n with hm0def
  have hm0lt : m0 < 2 ^ n := Theorem88d.encodeBits_lt δ0 n
  refine ⟨m0, hm0lt, ?_⟩
  rw [atomUEmpty_eq_zero_iff_genAtom]
  have hagree : ∀ j < n + 1, deltaOf (m0 + 2 ^ n) j = δ0 j := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hj']; exact Theorem88d.deltaOf_encodeBits δ0 n j hj'
    · rw [deltaOf_two_pow_add_self hm0lt, hδ0n]
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree]
  exact hAne

/-- **The `D`-side atom splits along any prepended index** (Scott's `Δ = idxSetₙ ∪ (Δ∖idxSetₙ)`,
pulled back through `DAtom`): needed to show that once the "negative refinement" of a nonempty atom
is empty, the atom already coincides with its own "positive refinement" outright. -/
theorem DAtom_union (i : ℕ) (pos neg : List ℕ) :
    DAtom (P0 P) pos neg = DAtom (P0 P) (i :: pos) neg ∪ DAtom (P0 P) pos (i :: neg) := by
  ext m
  simp only [mem_DAtom, Set.mem_union, List.mem_cons, forall_eq_or_imp]
  by_cases hm : (P0 P).X m ⊆ (P0 P).X i <;> tauto

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem datomDec_eq_zero (posC negC : ℕ) (h : DAtom (P0 P) (decodeList posC) (decodeList negC) ≠ ∅) :
    datomDec P (Nat.pair posC negC) = 0 := by
  have hle := datomDec_le_one P (Nat.pair posC negC)
  have hne : datomDec P (Nat.pair posC negC) ≠ 1 := fun he => h ((datomDec_spec P posC negC).mp he)
  omega

/-- Reducing modulo `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

/-- **The canonical "positive twin" at depth `n`** shares `k`'s own `(pos, neg, code)` triple, since
it agrees with `k` on every bit below `n` (`atomUCodeState_congr` applied to
`k % 2ⁿ`/`deltaOf_mod_two_pow_of_lt`/`deltaOf_add_two_pow_of_lt`). -/
theorem atomUCodeState_congr_twin (n k : ℕ) :
    atomUPos P n (k % 2 ^ n + 2 ^ n) = atomUPos P n k ∧
      atomUNeg P n (k % 2 ^ n + 2 ^ n) = atomUNeg P n k ∧
      atomUCode P n (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
  have hagree : ∀ i < n, deltaOf (k % 2 ^ n + 2 ^ n) i = deltaOf k i := by
    intro i hi
    rw [deltaOf_add_two_pow_of_lt _ hi, deltaOf_mod_two_pow_of_lt hi]
  exact atomUCodeState_congr P hagree

/-- **Uniqueness of a bit-source below `2ⁿ`**: two bit-sources agreeing on every bit below `n` and
both `< 2ⁿ` are equal (every bit at or above `n` is forced `false` by the bound, so agreement below
`n` becomes agreement everywhere, and `Nat.eq_of_testBit_eq` finishes). -/
theorem eq_of_deltaOf_agree_of_lt_two_pow {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hagree : ∀ l < n, deltaOf i l = deltaOf j l) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro l
  rw [← deltaOf_eq_testBit, ← deltaOf_eq_testBit]
  rcases Nat.lt_or_ge l n with hl | hl
  · exact hagree l hl
  · have hile : 2 ^ n ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_lt_two_pow (hi.trans_le hile),
      Nat.testBit_lt_two_pow (hj.trans_le hile)]

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (Domain.Recursive.appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

theorem presentedIntervals_decodeQPairList_appendCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (Domain.Recursive.appendCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∪ presentedIntervals (decodeQPairList c2) := by
  ext x
  simp only [presentedIntervals.mem, Set.mem_union]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rcases (mem_decodeQPairList_appendCode c1 c2 p).mp hp with hp' | hp'
    · exact Or.inl ⟨p, hp', h1, h2⟩
    · exact Or.inr ⟨p, hp', h1, h2⟩
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inl hp), h1, h2⟩
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inr hp), h1, h2⟩


section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


theorem primrec_atomBase : Nat.Primrec atomBase :=
  ((Nat.Primrec.id).pair ((Nat.Primrec.const 0).pair
    ((Nat.Primrec.const 0).pair (Nat.Primrec.const UmasterIdx)))).of_eq fun k => by
    unfold atomBase packState; simp only [id_eq]

end AtomCode

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_datomDec : Nat.Primrec (datomDec P) :=
  (primrec_isOne.comp (DAtom_recDecidable (P0 P)).choose_spec.1).of_eq fun _ => rfl
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


theorem primrec_stateCode : Nat.Primrec stateCode :=
  Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_stateNeg : Nat.Primrec stateNeg :=
  Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_statePos : Nat.Primrec statePos := Nat.Primrec.left.comp Nat.Primrec.right

theorem primrec_stateRem : Nat.Primrec stateRem := Nat.Primrec.left

end AtomCode

theorem primrec_unionUX : Nat.Primrec (fun t : ℕ => unionUX t.unpair.1 t.unpair.2) := by
  unfold unionUX
  exact (Domain.Recursive.primrec_appendCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


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

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_atomUCodeState : Nat.Primrec (atomUCodeState P) :=
  (Nat.Primrec.prec primrec_atomBase (primrec_atomStep (primrec_datomDec P))).of_eq fun _t => rfl

theorem primrec_atomUCode : Nat.Primrec (fun t : ℕ => atomUCode P t.unpair.1 t.unpair.2) :=
  (primrec_stateCode.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUNeg : Nat.Primrec (fun t : ℕ => atomUNeg P t.unpair.1 t.unpair.2) :=
  (primrec_stateNeg.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUPos : Nat.Primrec (fun t : ℕ => atomUPos P t.unpair.1 t.unpair.2) :=
  (primrec_statePos.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUEmpty : Nat.Primrec (fun t : ℕ => atomUEmpty P t.unpair.1 t.unpair.2) :=
  ((primrec_datomDec P).comp ((primrec_atomUPos P).pair (primrec_atomUNeg P))).of_eq
    fun _ => rfl

theorem primrec_yFoldStep : Nat.Primrec (yFoldStep P) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h2n : Nat.Primrec (fun w : ℕ => 2 ^ w.unpair.1) := primrec_two_pow hn
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 2 ^ w.unpair.1) :=
    primrec_add₂ hi h2n
  have hn1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) := Nat.Primrec.succ.comp hn
  have hempty : Nat.Primrec (fun w : ℕ =>
      atomUEmpty P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUEmpty P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcode : Nat.Primrec (fun w : ℕ =>
      atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUCode P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => unionUX w.unpair.2.unpair.2.unpair.2
      (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))) :=
    (primrec_unionUX.comp (hval.pair hcode)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (unionUX w.unpair.2.unpair.2.unpair.2
        (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))))
      (Nat.pair 1 (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)))) :=
    primrec_selectFn hfound
      ((Nat.Primrec.const 1).pair hunion)
      ((Nat.Primrec.const 1).pair hcode)
  exact (primrec_selectFn hempty hacc hinner).of_eq fun w => by unfold yFoldStep; simp only []

theorem primrec_yFold : Nat.Primrec (fun t : ℕ => yFold P t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0)) (primrec_yFoldStep P)).of_eq fun _ => rfl

theorem primrec_YseqCode : Nat.Primrec (YseqCode P) := by
  have h2n : Nat.Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow Nat.Primrec.id
  refine (Nat.Primrec.right.comp ((primrec_yFold P).comp (Nat.Primrec.id.pair h2n))).of_eq
    fun n => ?_
  show ((yFold P (Nat.pair n (2 ^ n)).unpair.1 (Nat.pair n (2 ^ n)).unpair.2)).unpair.2 = YseqCode P n
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

theorem UX_unionUX (n m : ℕ) : UX (unionUX n m) = UX n ∪ UX m := by
  have hmem : U.mem (presentedIntervals (decodeQPairList (Domain.Recursive.appendCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_appendCode]; exact U_mem_union_UX n m
  show presentedIntervals (decodeQPairList (canonCode (unionUX n m))) = UX n ∪ UX m
  unfold unionUX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hmem,
    presentedIntervals_decodeQPairList_appendCode]
  rfl

/-- **The membership form of `yFold`'s correctness**: once a non-junk bit-source has been found
below `N`, the running code's `UX`-image is exactly the union of the genuine (non-junk) atoms
seen so far. -/
theorem yFold_mem_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 →
      ∀ z : ℚ, z ∈ UX (yFold P n N).unpair.2 ↔
        ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) := by
  intro N
  induction N with
  | zero => intro h; simp [yFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [yFold_succ, yFoldStep_eq] at hfound1 ⊢
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((yFold_found_iff P n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (yFold P n N).unpair.1 = 1 := by
          have := yFold_found_le_one P n N; omega
        rw [hf1, selectFn_one, unpair_pair_snd, UX_unionUX, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)


theorem yFold_two_pow_found (n : ℕ) : (yFold P n (2 ^ n)).unpair.1 = 1 :=
  (yFold_found_iff P n (2 ^ n)).mpr (exists_atomUEmpty_zero P n)

/-- **The closed-form membership characterization of `YseqCode`** — the "Set-level closed form"
this part exists to supply: a point lies in `UX (YseqCode P n)` iff it lies in some genuine
(non-junk) depth-`(n+1)` atom with bit `n` forced `1`. -/
theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

/-- **General exclusion lemma**: if a bit-source `k'` is non-junk at depth `n`, and its own
canonical "positive twin" at depth `n + 1` (same bits below `n`, forcing bit `n` to `true`) is
junk, then `k'`'s own depth-`n` atom is disjoint from `YseqCode`'s entire union — no genuine
(non-junk) depth-`(n+1)` atom in the union can leak a point into it, whether that atom *is* `k'`'s
own excluded twin (immediate contradiction) or some *other* twin `i ≠ j` (disjoint at depth `n` by
`atomUCode_disjoint`, since distinct bit-sources below `2ⁿ` always disagree somewhere below `n`,
`eq_of_deltaOf_agree_of_lt_two_pow`). -/
theorem atomUCode_disjoint_YseqCode_of_posTwin_empty {n k' : ℕ} (hk' : atomUEmpty P n k' = 0)
    (hjunk : atomUEmpty P (n + 1) (k' % 2 ^ n + 2 ^ n) = 1) :
    UX (atomUCode P n k') ∩ UX (YseqCode P n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzB, hzY⟩
  obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
  set j := k' % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k' (Nat.two_pow_pos n)
  have hk'j : ∀ l < n, deltaOf k' l = deltaOf j l := by
    intro l hl; rw [hjdef, deltaOf_mod_two_pow_of_lt hl]
  by_cases hij : i = j
  · rw [hij] at hie; exact absurd hie (by omega)
  · have hdisagree : ∃ l < n, deltaOf (i + 2 ^ n) l ≠ deltaOf k' l := by
      by_contra hcon
      push Not at hcon
      apply hij
      apply eq_of_deltaOf_agree_of_lt_two_pow hilt hjlt
      intro l hl
      have h1 : deltaOf (i + 2 ^ n) l = deltaOf i l := deltaOf_add_two_pow_of_lt _ hl
      have h2 := hcon l hl
      rw [h1] at h2
      exact h2.trans (hk'j l hl)
    obtain ⟨l, hl, hlne⟩ := hdisagree
    have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') = ∅ :=
      atomUCode_disjoint P n (i + 2 ^ n) k' (atomUEmpty_zero_of_succ P hie) hk' ⟨l, hl, hlne⟩
    have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode.subset P hie hz
    have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') := ⟨hzB', hzB⟩
    rw [hd] at hzmem
    exact absurd hzmem (Set.mem_empty_iff_false z).mp

theorem atomUCode_succ_true {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = true) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) ∩ UX (YseqCode P n) := by
  set j := k % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  have hagree : ∀ i < n + 1, deltaOf k i = deltaOf (j + 2 ^ n) i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hi', hjdef, deltaOf_mod_two_pow_of_lt hi']
    · rw [deltaOf_two_pow_add_self hjlt, hδ]
  obtain ⟨hpos_eq, hneg_eq, hcode_eq⟩ := atomUCodeState_congr P hagree
  have hempty_eq : atomUEmpty P (n + 1) (j + 2 ^ n) = 0 := by
    have heq : atomUEmpty P (n + 1) (j + 2 ^ n) = atomUEmpty P (n + 1) k := by
      unfold atomUEmpty; rw [hpos_eq, hneg_eq]
    rw [heq]; exact hne
  apply Set.Subset.antisymm
  · have hsub1 : UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := atomUCode.subset P hne
    have hsub2 : UX (atomUCode P (n + 1) k) ⊆ UX (YseqCode P n) := by
      rw [hcode_eq]
      intro z hz
      exact (mem_UX_YseqCode_iff P n z).mpr ⟨j, hjlt, hempty_eq, hz⟩
    exact Set.subset_inter hsub1 hsub2
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
    by_cases hagree' : ∀ p < n, deltaOf (i + 2 ^ n) p = deltaOf k p
    · have hagreeFull : ∀ l < n + 1, deltaOf (i + 2 ^ n) l = deltaOf k l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
        · exact hagree' l hl'
        · rw [deltaOf_two_pow_add_self hilt, hδ]
      have hcode_eq'' : atomUCode P (n + 1) (i + 2 ^ n) = atomUCode P (n + 1) k :=
        (atomUCodeState_congr P hagreeFull).2.2
      rw [← hcode_eq'']; exact hz
    · push Not at hagree'
      obtain ⟨l, hl, hlne⟩ := hagree'
      have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) = ∅ :=
        atomUCode_disjoint P n (i + 2 ^ n) k (atomUEmpty_zero_of_succ P hie)
          (atomUEmpty_zero_of_succ P hne) ⟨l, hl, hlne⟩
      have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode.subset P hie hz
      have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) := ⟨hzB', hzB⟩
      rw [hd] at hzmem
      exact absurd hzmem (Set.mem_empty_iff_false z).mp

/-- **The junction lemma**: once a bit-source's atom is still non-empty at depth `n` but becomes
junk at depth `n + 1`, `genAtom`'s corresponding step (against `Yc P`/`U.master`) is already
empty. Two cases on `deltaOf k n`: `true` reduces directly to
`atomUCode_disjoint_YseqCode_of_posTwin_empty` (`k` already *is* its own positive twin); `false`
needs the extra fact that the depth-`n` atom's own code is *unchanged* by its positive twin (since
the "negative refinement" being `D`-side empty forces the whole atom into the positive side,
`DAtom_union`), so `atomUCode_succ_true` at the twin identifies `atomUCode P n k` with the
intersection against `YseqCode`'s union outright, i.e. `UX (atomUCode P n k) ⊆ Yc P n`. -/
theorem atomUCode_inter_succ_empty_of_junk {n k : ℕ} (hn0 : atomUEmpty P n k = 0)
    (hjunk : atomUEmpty P (n + 1) k = 1) :
    UX (atomUCode P n k) ∩ (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅ := by
  -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
  rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
  · -- `k` itself already has bit `n` set: `k` is (mod `2 ^ (n + 1)`) its own positive twin.
    have hjlt0 : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    have hagree : ∀ l < n + 1, deltaOf (k % 2 ^ n + 2 ^ n) l = deltaOf k l := by
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [deltaOf_add_two_pow_of_lt _ hl', deltaOf_mod_two_pow_of_lt hl']
      · rw [deltaOf_two_pow_add_self hjlt0, hδ]
    obtain ⟨hp, hnge, -⟩ := atomUCodeState_congr P hagree
    have htwinJunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by
      unfold atomUEmpty
      rw [hp, hnge]
      exact hjunk
    rw [ite_eq_left hδ]
    exact atomUCode_disjoint_YseqCode_of_posTwin_empty P hn0 htwinJunk
  · -- `k` has bit `n` unset: the "negative refinement" alone is empty, so `k`'s own atom already
    -- coincides with its positive twin's atom (`DAtom_union`), which forces junk at `n + 1`.
    have hbit0 : (k / 2 ^ n) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
      · exact hh
      · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
    have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
      have h := hjunk
      rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
      exact h
    have hJempty : DAtom (P0 P) (decodeList (atomUPos P n k))
        (n :: decodeList (atomUNeg P n k)) = ∅ := by
      have h := (datomDec_spec P (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)).mp hempJ
      rwa [decodeList_succ, unpair_pair_fst, unpair_pair_snd] at h
    have hDunion := DAtom_union P n (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))
    have hIeqAll : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (n :: decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
      rw [hDunion, hJempty, Set.union_empty]
    have hIeqAll' : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (decodeList (Nat.pair n (atomUPos P n k) + 1)) (decodeList (atomUNeg P n k)) := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]; exact hIeqAll
    have hne0 : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) ≠ ∅ := by
      intro hcon
      have := (atomUEmpty_eq_one_iff P n k).mpr hcon
      omega
    have hemptyI0 : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
      apply datomDec_eq_zero
      rw [← hIeqAll']
      exact hne0
    have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
    have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
      have hh := deltaOf_two_pow_add_self hjlt
      rw [deltaOf_eq_true_iff] at hh
      exact hh
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by
      rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
      exact hemptyI0
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
      rw [atomUCode.succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, hemptyI0, selectFn_zero,
        htwinCode, hempJ, selectFn_one]
    rw [htwinCodeVal, htwinCode] at hkey
    have hsub : UX (atomUCode P n k) ⊆ Yc P n := by
      intro z hz
      have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := by rw [← hkey]; exact hz
      exact hz'.2
    rw [ite_eq_right (by simp [hδ])]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz1, -, hz2⟩
    exact hz2 (hsub hz1)

/-- **The closed form, "false"-branch** (mirroring `Theorem88.lean`'s `atomU_succ_eq`'s `else`
case): for non-junk `k` with bit `n` forced `false`, the depth-`(n+1)` atom is the depth-`n` atom
*minus* `YseqCode`. Two sub-cases on whether `k`'s own "positive twin" (bits agreeing below `n`,
bit `n` forced `true`) is itself junk: if junk, the whole depth-`n` atom is already disjoint from
`YseqCode`'s union (`atomUCode_disjoint_YseqCode_of_posTwin_empty`), so subtracting it changes
nothing; if non-junk, the twin's own code is literally `splitULeft (atomUCode P n k)` (unfolding
both `atomUCode.succ`'s at the shared ancestor), so `atomUCode_succ_true` applied to the twin
identifies `splitULeft`'s image with `YseqCode`'s contribution, and `splitU_union`/`splitU_disjoint`
finish the algebra `UX(splitURight c) = UX c \ UX(splitULeft c)`. -/
theorem atomUCode_succ_false {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = false) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
  have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
  have hbit0 : (k / 2 ^ n) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
    · exact hh
    · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
  have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
    have h := hne
    rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
    exact h
  have hncode : atomUCode P (n + 1) k = selectFn
      (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
      (atomUCode P n k) (splitURight (atomUCode P n k)) := by
    rw [atomUCode.succ, hbit0, selectFn_zero, hempJ, selectFn_zero]
  have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
    have hh := deltaOf_two_pow_add_self hjlt
    rw [deltaOf_eq_true_iff] at hh
    exact hh
  have htwinEmpty : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) =
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) := by
    rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
  have hIle := datomDec_le_one P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))
  rcases (by omega :
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 ∨
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1) with hI | hI
  · -- Genuine split at the shared ancestor: the twin's own code is `splitULeft (atomUCode P n k)`.
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = splitULeft (atomUCode P n k) := by
      rw [atomUCode.succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, htwinCode, hI, selectFn_zero,
        hempJ, selectFn_zero]
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by rw [htwinEmpty, hI]
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    rw [htwinCodeVal, htwinCode] at hkey
    have hunion := splitU_union (atomUCode P n k)
    have hdisj := splitU_disjoint (atomUCode P n k)
    have hUXeq : UX (splitURight (atomUCode P n k)) =
        UX (atomUCode P n k) \ UX (splitULeft (atomUCode P n k)) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨?_, fun hzL => ?_⟩
        · rw [← hunion]; exact Set.mem_union_right _ hz
        · have hz' : z ∈ UX (splitULeft (atomUCode P n k)) ∩ UX (splitURight (atomUCode P n k)) :=
            ⟨hzL, hz⟩
          rw [hdisj] at hz'
          exact hz'
      · rintro z ⟨hzC, hznL⟩
        rw [← hunion] at hzC
        exact hzC.resolve_left hznL
    rw [hncode, hI, selectFn_zero, hUXeq, hkey]
    apply Set.Subset.antisymm
    · rintro z ⟨hzC, hznCY⟩
      exact ⟨hzC, fun hzY => hznCY ⟨hzC, hzY⟩⟩
    · rintro z ⟨hzC, hznY⟩
      exact ⟨hzC, fun hzY => hznY hzY.2⟩
  · -- Junk twin: the whole depth-`n` atom is already disjoint from `YseqCode`'s union.
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by rw [htwinEmpty, hI]
    have hk : atomUEmpty P n k = 0 := atomUEmpty_zero_of_succ P hne
    have hcdisj : UX (atomUCode P n k) ∩ UX (YseqCode P n) = ∅ :=
      atomUCode_disjoint_YseqCode_of_posTwin_empty P hk htwinNonjunk
    have hEq : UX (atomUCode P n k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨hz, fun hzY => ?_⟩
        have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := ⟨hz, hzY⟩
        rw [hcdisj] at hz'
        exact hz'
      · exact Set.sdiff_subset
    rw [hncode, hI, selectFn_one]
    exact hEq

/-- **The closed-form correspondence** (mirrors `Theorem88.lean`'s `atomU_eq_genAtom`): whenever
`k`'s bit-source is still `D`-side non-empty at depth `n`, the `U`-code `atomUCode P n k` is
*exactly* the generic atom built from `Yc P`/`U.master` — proved by induction, using
`atomUCode_succ_true`/`atomUCode_succ_false` to match `genAtom`'s own recursive step verbatim. -/
theorem atomUCode_eq_genAtomYseqCode (k : ℕ) :
    ∀ n, atomUEmpty P n k = 0 → UX (atomUCode P n k) = genAtom (Yc P) U.master (deltaOf k) n := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [atomUCode.zero, UX_UmasterIdx]
    rfl
  | succ n ih =>
    intro hne
    have ihn := ih (atomUEmpty_zero_of_succ P hne)
    -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ Yc P n := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_true P hne hδ]
      rfl
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ (U.master \ Yc P n) := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_false P hne hδ]
      have hsub : UX (atomUCode P n k) ⊆ U.master := by
        rw [ihn]; exact genAtom_subset (Yc P) U.master (deltaOf k) n
      apply Set.Subset.antisymm
      · intro z hz; exact ⟨hz.1, hsub hz.1, hz.2⟩
      · rintro z ⟨hz1, -, hz2⟩; exact ⟨hz1, hz2⟩

/-- **`Yc P`'s `genAtom`-emptiness matches `atomUEmpty` exactly** (the code-native analogue of
`atomU_invariant`'s emptiness-matching clause "(■)"): combines `atomUCode_eq_genAtomYseqCode`
(non-junk, giving a nonempty `UX`-image) with `atomUCode_inter_succ_empty_of_junk` (the genuine
transition to junk) by induction on `n`. -/
theorem genAtom_Yc_empty_iff (n k : ℕ) :
    genAtom (Yc P) U.master (deltaOf k) n = ∅ ↔ atomUEmpty P n k = 1 := by
  induction n with
  | zero =>
    have h0 : atomUEmpty P 0 k = 0 := by
      have hne : genAtom (idxSet (e P)) Set.univ (deltaOf k) 0 ≠ ∅ := by
        show (Set.univ : Set ℕ) ≠ ∅
        exact Set.univ_nonempty.ne_empty
      exact (atomUEmpty_eq_zero_iff_genAtom P 0 k).mpr hne
    constructor
    · intro h
      exact absurd h (Set.Nonempty.ne_empty U.master_mem.2.1)
    · intro h; omega
  | succ n ih =>
    have hle : atomUEmpty P (n + 1) k ≤ 1 := datomDec_le_one P _
    rcases (by omega : atomUEmpty P (n + 1) k = 0 ∨ atomUEmpty P (n + 1) k = 1) with h1 | h1
    · have heq' := atomUCode_eq_genAtomYseqCode P k (n + 1) h1
      constructor
      · intro hempty
        rw [← heq'] at hempty
        exact absurd hempty (U_mem_UX _).2.1.ne_empty
      · intro hcontra; omega
    · by_cases hn0 : atomUEmpty P n k = 0
      · have heq := atomUCode_eq_genAtomYseqCode P k n hn0
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [← heq]
          exact atomUCode_inter_succ_empty_of_junk P hn0 h1
        exact ⟨fun _ => h1, fun _ => hempty⟩
      · push Not at hn0
        have hle0 : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
        have hn1 : atomUEmpty P n k = 1 := by omega
        have hprev : genAtom (Yc P) U.master (deltaOf k) n = ∅ := ih.mpr hn1
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [hprev, Set.empty_inter]
        exact ⟨fun _ => h1, fun _ => hempty⟩

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Yc_subset_master (n : ℕ) : Yc P n ⊆ U.master := (U_mem_UX (YseqCode P n)).2.2

/-- **`Yc P 0 = U.master`** (Scott's convention `Y₀ = U.master`, matching `Yseq_zero_eq_master`):
the unique bit-source realizing depth `1` with bit `0` set is `k = 1`, whose atom is non-junk
(`idxSet (e P) 0 = Set.univ`, so the "positive" constraint at index `0` is vacuous) and whose code
is literally `UmasterIdx`, since the *negative* sibling constraint (`DAtom (P0 P) [] [0]`) is
already empty — freezing `atomUCode` unchanged through the step (mirrors `atomUCode.subset`'s own
"carry unchanged" branch, here made into an equality). -/
theorem Yc_zero_eq_master : Yc P 0 = U.master := by
  have hidx0 : idxSet (e P) 0 = Set.univ := idxSet_zero D (e P) (hcover P) (he0 P)
  have h01 : atomUEmpty P 1 1 = 0 := by
    apply (atomUEmpty_eq_zero_iff_genAtom P 1 1).mpr
    show genAtom (idxSet (e P)) Set.univ (deltaOf 1) 0 ∩
      (if deltaOf 1 0 then idxSet (e P) 0 else Set.univ \ idxSet (e P) 0) ≠ ∅
    have hδ : deltaOf 1 0 = true := by decide
    rw [hδ, ite_eq_left rfl]
    show (Set.univ : Set ℕ) ∩ idxSet (e P) 0 ≠ ∅
    rw [Set.univ_inter, hidx0]
    exact Set.univ_nonempty.ne_empty
  have hmem : Yc P 0 = UX (atomUCode P 1 1) := by
    unfold Yc
    ext z
    rw [mem_UX_YseqCode_iff]
    constructor
    · rintro ⟨i, hilt, hie, hz⟩
      have hi0 : i = 0 := by have := hilt; omega
      rwa [hi0] at hz
    · intro hz
      exact ⟨0, by norm_num, h01, hz⟩
  rw [hmem]
  have hnn : DAtom (P0 P) [] [] = Set.univ := by unfold DAtom; simp [IPos_nil]
  have hcode : atomUCode P 1 1 = UmasterIdx := by
    have hbit : (1 / 2 ^ (0 : ℕ)) % 2 = 1 := by norm_num
    rw [atomUCode.succ, atomUPos_zero, atomUNeg_zero, hbit, selectFn_one]
    have hposEmpty : datomDec P (Nat.pair (Nat.pair 0 0 + 1) 0) = 0 := by
      apply datomDec_eq_zero
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [0] [] ≠ ∅
      rw [DAtom_cons_pos, hnn, Set.inter_univ, hidx0]
      exact Set.univ_nonempty.ne_empty
    rw [hposEmpty, selectFn_zero]
    have hnegEmpty : datomDec P (Nat.pair 0 (Nat.pair 0 0 + 1)) = 1 := by
      apply (datomDec_spec P _ _).mpr
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [] [0] = ∅
      rw [DAtom_cons_neg, hnn, Set.inter_univ, hidx0, Set.sdiff_self]
    rw [hnegEmpty, selectFn_one, atomUCode.zero]
  rw [hcode, UX_UmasterIdx]

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

/-- **The `genAtom`-emptiness core, for arbitrary `δ : ℕ → Bool`.** Realizes `δ`'s first `n` bits
as `deltaOf (encodeBits δ n)` (`genAtom_congr`), then invokes `genAtom_Yc_empty_iff`/
`atomUEmpty_eq_one_iff_genAtom` at that specific bit-source. -/
theorem hcoreIdxYc (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔ genAtom (Yc P) U.master δ n = ∅ := by
  set k := encodeBits δ n with hkdef
  have hagree : ∀ i < n, δ i = deltaOf k i := fun i hi => (deltaOf_encodeBits δ n i hi).symm
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree, genAtom_congr (Yc P) U.master hagree,
    ← atomUEmpty_eq_one_iff_genAtom, genAtom_Yc_empty_iff]

theorem inclK_i_recDecidable_code :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem inclK_j_recDecidable_code :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem transfer_dir_idxYc {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
    (M2 : Set β2) (hcore : ∀ δ n, genAtom Z1 M1 δ n = ∅ ↔ genAtom Z2 M2 δ n = ∅)
    {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n)
    (hne : {x ∈ M1 | ∀ p ∈ cs, (p.2 = true ↔ x ∈ Z1 p.1)}.Nonempty) :
    {y ∈ M2 | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Z2 p.1)}.Nonempty := by
  classical
  obtain ⟨x, hxM, hxcs⟩ := hne
  set δ0 : ℕ → Bool := fun k => decide (x ∈ Z1 k) with hδ0def
  have hX1 : x ∈ genAtom Z1 M1 δ0 n := genAtom_self Z1 M1 hxM n
  have hne1 : (genAtom Z1 M1 δ0 n).Nonempty := ⟨x, hX1⟩
  have hne2 : (genAtom Z2 M2 δ0 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h2 => hne1.ne_empty ((hcore δ0 n).mpr h2)
  obtain ⟨y, hy⟩ := hne2
  refine ⟨y, genAtom_subset Z2 M2 δ0 n hy, fun p hp => ?_⟩
  have hforward := genAtom_forward hy p.1 (hn p hp)
  have hbeq : δ0 p.1 = p.2 := by
    show decide (x ∈ Z1 p.1) = p.2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hxcs p hp).symm
  rwa [hbeq] at hforward

theorem transfer_empty_iff_idxYc {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ cs, (p.2 = true ↔ x ∈ idxSet (e P) p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yc P p.1)}.Nonempty :=
  ⟨transfer_dir_idxYc (idxSet (e P)) Set.univ (Yc P) U.master (hcoreIdxYc P) hn,
    transfer_dir_idxYc (Yc P) U.master (idxSet (e P)) Set.univ (fun δ n => (hcoreIdxYc P δ n).symm)
      hn⟩

theorem transfer_double_subset_iff_idxYc (i j k : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      U.master ∩ Yc P i ∩ Yc P j ⊆ Yc P k := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)}
      = ((Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j) \ idxSet (e P) k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i ∩ Yc P j) \ Yc P k := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∈ Yc P j := (hcs (j, true) (by simp)).mp rfl
      have h3 : y ∉ Yc P k := fun hmem =>
        absurd ((hcs (k, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
    · rintro ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h3⟩
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_inter_empty_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j = ∅ ↔
      U.master ∩ Yc P i ∩ Yc P j = ∅ := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = U.master ∩ Yc P i ∩ Yc P j := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      exact ⟨⟨hyM, (hcs (i, true) (by simp)).mp rfl⟩, (hcs (j, true) (by simp)).mp rfl⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_subset_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ⊆ idxSet (e P) j ↔
      U.master ∩ Yc P i ⊆ Yc P j := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = ((Set.univ : Set ℕ) ∩ idxSet (e P) i) \ idxSet (e P) j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i) \ Yc P j := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∉ Yc P j := fun hmem =>
        absurd ((hcs (j, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨hyM, h1⟩, h2⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h2⟩
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- **`idxSet e i ⊆ idxSet e j ↔ Yc P i ⊆ Yc P j`.** The `Δ = Set.univ`/`Yc P i ⊆ U.master`
simplification of `transfer_subset_iff_idxYc`, matching `Theorem88a.lean`'s `embed_subset_iff`. -/
theorem embed_subset_iff_code (i j : ℕ) : idxSet (e P) i ⊆ idxSet (e P) j ↔ Yc P i ⊆ Yc P j := by
  have := transfer_subset_iff_idxYc P i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this

theorem embed_eq_iff_code (i j : ℕ) : idxSet (e P) i = idxSet (e P) j ↔ Yc P i = Yc P j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mp h.subset)
      ((embed_subset_iff_code P j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mpr h.subset)
      ((embed_subset_iff_code P j i).mpr h.symm.subset)⟩

/-- **`e P i = e P j ↔ Yc P i = Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_eq_iff`. -/
theorem embed_eq_iff_raw_code (i j : ℕ) : e P i = e P j ↔ Yc P i = Yc P j := by
  rw [← idxSet_eq_iff (e P) i j]
  exact embed_eq_iff_code P i j

/-- **`e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_subset_iff`, built from the idxSet-level `embed_subset_iff_code` via `idxSet_subset_iff`. -/
theorem embed_subset_iff_raw_code (i j : ℕ) : e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j := by
  rw [← idxSet_subset_iff (e P) i j]
  exact embed_subset_iff_code P i j

/-- **`∃ k, Yc P k ⊆ Yc P i ∩ Yc P j` is recursively decidable in `(i, j)`.** Transfers
(`embed_subset_iff_raw_code`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate. -/
theorem DprimeUCode_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yc P k ⊆ Yc P i ∩ Yc P j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff_raw_code P k t.unpair.1, ← embed_subset_iff_raw_code P k t.unpair.2])

theorem transfer_inter_eq_iff_idxYc (i j k : ℕ) :
    idxSet (e P) i ∩ idxSet (e P) j = idxSet (e P) k ↔ Yc P i ∩ Yc P j = Yc P k := by
  have h1 : idxSet (e P) k ⊆ idxSet (e P) i ↔ Yc P k ⊆ Yc P i := embed_subset_iff_code P k i
  have h2 : idxSet (e P) k ⊆ idxSet (e P) j ↔ Yc P k ⊆ Yc P j := embed_subset_iff_code P k j
  have h3 : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      Yc P i ∩ Yc P j ⊆ Yc P k := by
    have := transfer_double_subset_iff_idxYc P i j k
    rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this
  constructor
  · intro heq
    have hki : idxSet (e P) k ⊆ idxSet (e P) i := heq ▸ Set.inter_subset_left
    have hkj : idxSet (e P) k ⊆ idxSet (e P) j := heq ▸ Set.inter_subset_right
    have hijk : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yc P k ⊆ Yc P i := by rw [← heq]; exact Set.inter_subset_left
    have hkj : Yc P k ⊆ Yc P j := by rw [← heq]; exact Set.inter_subset_right
    have hijk : Yc P i ∩ Yc P j ⊆ Yc P k := by rw [heq]
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-- **`Yc P i ∩ Yc P j = Yc P k` is recursively decidable in `(i, j, k)`.** Transfers
(`transfer_inter_eq_iff_idxYc`) to the `idxSet`-level equation, which `idxSet_inter_eq_iff_DAtom`
reduces to two `incl_computable` queries and one `DAtom_recDecidable` query. -/
theorem DprimeUCode_interEq_computable :
    RecDecidable₃ (fun i j k => Yc P i ∩ Yc P j = Yc P k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable_code P |>.and (inclK_j_recDecidable_code P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff_idxYc P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2,
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

/-- **The intersection index transfers.** `(P0 P).inter n m` (Scott's own primitive-recursive
intersection index for `D`, reused verbatim) also indexes `Yc P n ∩ Yc P m` whenever that
intersection is consistent. -/
theorem DprimeUCode_inter_spec {n m : ℕ} (h : ∃ k, Yc P k ⊆ Yc P n ∩ Yc P m) :
    Yc P ((P0 P).inter n m) = Yc P n ∩ Yc P m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff_raw_code P k n).mpr hk.1)
      ((embed_subset_iff_raw_code P k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff_idxYc P n m ((P0 P).inter n m)).mp hidx).symm

theorem exists_inter_index_of_dmem_code {i j : ℕ} (hDij : D.mem (e P i ∩ e P j)) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  obtain ⟨m, hm⟩ := (hcover P (e P i ∩ e P j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff_idxYc P i j m).mp (idxSet_inter_of_inter_eq (e P) hm)⟩

/-- **`D'' := DprimeUCode`**: the neighbourhood system generated by `{Yc P n ∣ n ∈ ℕ}`, genuinely
code-driven (`Yc P n = UX (YseqCode P n)`), mirroring `Theorem88a.lean`'s `DprimeU` construction. -/
noncomputable def DprimeUCode : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yc P n
  master := U.master
  master_nonempty := U.master_nonempty
  master_mem := ⟨0, (Yc_zero_eq_master P).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yc_subset_master P n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e P k ⊆ e P i := (embed_subset_iff_raw_code P k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e P k ⊆ e P j := (embed_subset_iff_raw_code P k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem_code P
      (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
        (D_mem_e D (e P) (hcover P) k) (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

/-- **Theorem 8.8(b)(vii)(3), presentation half.** `D''` (`DprimeUCode P`, genuinely code-driven:
`X n := Yc P n = UX (YseqCode P n)`) is effectively given, with master index `0`. Its two index
relations and intersection index are reused **unchanged** from `P0 P`; only the carrier family
changed from `Yidx (e P)` (Part 6's classical choice-built sets) to `Yc P` (this file's
`Nat.Primrec`-tracked codes). -/
noncomputable def DprimeUCodePresentation : ComputablePresentation (DprimeUCode P) where
  X n := Yc P n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeUCode_interEq_computable P
  cons_computable := DprimeUCode_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeUCode_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yc_zero_eq_master P

theorem exists_inter_index_of_nonempty_code {i j : ℕ} (hne : (Yc P i ∩ Yc P j).Nonempty) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  have hne' : (idxSet (e P) i ∩ idxSet (e P) j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff_idxYc P i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem_code P
    (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
      (D_mem_e D (e P) (hcover P) k) (Set.subset_inter hki hkj))

/-- **`D'' ◁ U`.** -/
theorem DprimeUCode_subsystem : DprimeUCode P ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact (U_mem_UX (YseqCode P n))
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty_code P hUmem.2.1
    exact ⟨m, hYeq⟩

/-- **Pullback**: the `D`-filter induced by a `D''`-filter `y`. -/
def toDCode (y : (DprimeUCode P).Element) : D.Element where
  mem S := ∃ n, S = e P n ∧ y.mem (Yc P n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D (e P) (hcover P) n
  master_mem := ⟨0, (he0 P).symm, by rw [Yc_zero_eq_master P]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeUCode P).mem (Yc P i ∩ Yc P j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty_code P
      ((DprimeUCode_subsystem P).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover P T).mp hDT
    have hYij : Yc P i ⊆ Yc P j := (embed_subset_iff_raw_code P i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

/-- **Pushforward**: the `D''`-filter induced by a `D`-filter `x`. -/
def toDprimeUCode (x : D.Element) : (DprimeUCode P).Element where
  mem Y := ∃ n, Y = Yc P n ∧ x.mem (e P n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yc_zero_eq_master P).symm, by rw [he0 P]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem_code P (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e P i ⊆ e P j := (embed_subset_iff_raw_code P i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D (e P) (hcover P) j) heij⟩

/-- **The order isomorphism `D.Element ≃o D''.Element`.** -/
noncomputable def domainIsoCode : DomainIso D (DprimeUCode P) where
  toFun := toDprimeUCode P
  invFun := toDCode P
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hxS)
      have hxn : x.mem (e P n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeUCode P x).mem (Yc P n))
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

/-- **Theorem 8.8(b)(vii)(3), full statement.** `D''` is effectively given, `D ≅ᴰ D''`, and
`D'' ◁ U`. -/
theorem DprimeUCode_isEffectivelyGiven : (DprimeUCode P).IsEffectivelyGiven :=
  ⟨DprimeUCodePresentation P⟩

/-- **Theorem 8.8(b)(vii)(3), isomorphism half.** `D ≅ᴰ D''`. -/
theorem isomorphic_DprimeUCode : D ≅ᴰ DprimeUCode P := ⟨domainIsoCode P⟩

/-- **The injection `i : D'' → U` is computable.** `i`'s relation `Yc P n \, i \, UX m` reduces to
the raw code-level subset test `UX (YseqCode P n) ⊆ UX m`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the first argument. -/
theorem DprimeUCode_inj_isComputableMap :
    ComputableMap (DprimeUCodePresentation P) UComputablePresentation
      (DprimeUCode_subsystem P).inj := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (YseqCode P t.unpair.1) t.unpair.2) :=
    Nat.Primrec.pair ((primrec_YseqCode P).comp Nat.Primrec.left) Nat.Primrec.right
  have hp : RecDecidable (fun t : ℕ => UX (YseqCode P t.unpair.1) ⊆ UX t.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).inj.rel (Yc P t.unpair.1) (UX t.unpair.2) ↔ _
  rw [Subsystem.inj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨⟨t.unpair.1, rfl⟩, U_mem_UX _, hsub⟩⟩

/-- **The projection `j : U → D''` is computable.** `j`'s relation `UX m \, j \, Yc P n` reduces to
the raw code-level subset test `UX m ⊆ UX (YseqCode P n)`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the second argument. -/
theorem DprimeUCode_proj_isComputableMap :
    ComputableMap UComputablePresentation (DprimeUCodePresentation P)
      (DprimeUCode_subsystem P).proj := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (YseqCode P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((primrec_YseqCode P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => UX t.unpair.1 ⊆ UX (YseqCode P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).proj.rel (UX t.unpair.1) (Yc P t.unpair.2) ↔ _
  rw [Subsystem.proj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨U_mem_UX _, ⟨t.unpair.2, rfl⟩, hsub⟩⟩

/-- **Theorem 8.8(b)(vii)(4), full statement.** The projection pair witnessing `D'' ◁ U` (Proposition
6.12, applied to `DprimeUCode_subsystem P : DprimeUCode P ◁ U`) is computable in both directions
relative to `D''`'s own presentation (`DprimeUCodePresentation`) and `U`'s presentation
(`UComputablePresentation`) — the headline claim of Theorem 8.8(b)(vii). -/
theorem DprimeUCode_projectionPair_isComputable :
    ComputableMap (DprimeUCodePresentation P) UComputablePresentation
        (DprimeUCode_subsystem P).inj ∧
      ComputableMap UComputablePresentation (DprimeUCodePresentation P)
        (DprimeUCode_subsystem P).proj :=
  ⟨DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end

open NeighborhoodSystem Domain.Recursive

/-- **Theorem 8.8(b) (Scott 1981, PRG-19), final assembly.** If `D` is effectively given (via a
`ComputablePresentation P`), the general universality of `U` (Theorem 8.8(a)) can be witnessed by a
`D' : NeighborhoodSystem ℚ` that is *itself* effectively given (`P' : ComputablePresentation D'`),
isomorphic to `D`, a subsystem of `U`, **and** whose projection pair `i := (D' ◁ U).inj`,
`j := (D' ◁ U).proj` (Proposition 6.12) is computable in both directions relative to `P'` and `U`'s
own presentation `UComputablePresentation`. -/
theorem theorem_8_8_b {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (D' : NeighborhoodSystem ℚ) (P' : ComputablePresentation D') (h : D' ◁ U),
      (D ≅ᴰ D') ∧
        ComputableMap P' UComputablePresentation h.inj ∧
        ComputableMap UComputablePresentation P' h.proj :=
  ⟨DprimeUCode P, DprimeUCodePresentation P, DprimeUCode_subsystem P,
    isomorphic_DprimeUCode P, DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c), Part 6 of 6 — final assembly.** A computable approximable self-map `a` of an
effectively given `V` (via `P`) makes `fixedNbhd a` effectively given: package Parts 1–5's `D_X`/
`D_inter` enumeration, instantiated at concrete witnesses `qChar` (Part 1) and `cons` (`P`'s own
`cons_computable`), into a `ComputablePresentation (fixedNbhd a)`. -/
theorem fixedNbhd_isEffectivelyGiven {P : ComputablePresentation V} {a : ApproximableMap V V}
    (hcomp : ComputableMap P P a) : (fixedNbhd a).IsEffectivelyGiven := by
  obtain ⟨qChar, hqCharp, hqChar⟩ := diagFixed_exists_qChar hcomp
  obtain ⟨cons, hconsp, hconse⟩ := P.cons_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have h := hconse (Nat.pair n m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    exact h.symm
  refine ⟨{
    X := D_X P qChar cons
    mem_X := D_X_mem hqChar hcons
    surj := fun hY => D_X_surj hqChar hcons hY
    interEq_computable := D_X_interEq_computable P qChar cons hqCharp hconsp
    cons_computable := D_X_cons_computable P qChar cons hqChar hcons hqCharp hconsp
    inter := D_inter
    inter_primrec := D_inter_primrec
    inter_spec := fun h => D_X_inter_spec hcons h
    masterIdx := 0
    masterIdx_spec := ?_ }⟩
  show D_X P qChar cons 0 = V.master
  show P.X (myFoldCode P qChar cons 0) = V.master
  rw [myFoldCode_eq, decodeList_zero, myFold_nil, P.masterIdx_spec]

/-- **Theorem 8.8(c) (Scott 1981, PRG-19), headline.** If `a : U → U` is a computable, finitary
projection of the universal domain, then `{Y ∈ U ∣ Y a Y}` is effectively given (and, unconditionally
by Theorem 8.5, a subsystem of `U`). As in Theorem 8.6(c)'s converse, `hfin` is carried in the
signature to match Scott's stated hypothesis on `a`, but is **not** actually needed by this
implication — only `hcomp` drives the effectiveness argument; this is called out here rather than
silently dropping the hypothesis. -/
theorem theorem_8_8_c {a : ApproximableMap U U} (_hfin : FinitaryProjection a)
    (hcomp : ComputableMap UComputablePresentation UComputablePresentation a) :
    (fixedNbhd a).IsEffectivelyGiven ∧ fixedNbhd a ◁ U :=
  ⟨fixedNbhd_isEffectivelyGiven hcomp, fixedNbhd_subsystem a⟩

end
open NeighborhoodSystem ApproximableMap Exercise326

/-- Every `𝒰`-neighbourhood is non-empty (built into Definition 8.7). -/
theorem U_mem_nonempty : ∀ X, U.mem X → X.Nonempty := fun _ hX => hX.2.1

/-- `𝒰 → 𝒰` is effectively given (Theorem 7.5, applied to `U`'s own presentation twice). -/
theorem funSpaceUU_isEffectivelyGiven : (funSpace U U).IsEffectivelyGiven :=
  funSpace_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 → 𝒰`. -/
noncomputable def funSpaceUUPresentation : ComputablePresentation (funSpace U U) :=
  funSpaceUU_isEffectivelyGiven.some

/-- **`λf. b∘f∘a : (𝒰→𝒰) → (𝒰→𝒰)`**, uncurried as `b ∘ eval ∘ (id ×ₘ a)`. -/
noncomputable def lamComb (a b : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a)))

/-- `𝒰 × 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem prodUU_isEffectivelyGiven : (prod U U).IsEffectivelyGiven :=
  prod_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 × 𝒰`. -/
noncomputable def prodUUPresentation : ComputablePresentation (prod U U) :=
  prodUU_isEffectivelyGiven.some

/-- `𝒰 + 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem sumUU_isEffectivelyGiven :
    (sum U U U_mem_nonempty U_mem_nonempty).IsEffectivelyGiven :=
  sum_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 + 𝒰`. -/
noncomputable def sumUUPresentation : ComputablePresentation (sum U U U_mem_nonempty U_mem_nonempty) :=
  sumUU_isEffectivelyGiven.some


section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`isoInj : D → D''`**, Theorem 2.7 applied to `domainIsoCode P`. -/
noncomputable def isoInj : ApproximableMap D (DprimeUCode P) := ofIso (domainIsoCode P)

/-- **`isoProj : D'' → D`**, Theorem 2.7 applied to the inverse iso. -/
noncomputable def isoProj : ApproximableMap (DprimeUCode P) D := ofIso (domainIsoCode P).symm

/-- `isoInj ∘ isoProj = I_D''`. -/
theorem isoInj_comp_isoProj : (isoInj P).comp (isoProj P) = idMap (DprimeUCode P) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (isoInj P).toElementMap ((isoProj P).toElementMap y) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
    toElementMap_idMap]

/-- **`isoInj`'s relation at raw indices reduces to a single reindexed inclusion.** `n := b` is always
a valid witness (`Yc P b = Yc P b`), and any *other* witness `n` with `Yc P b = Yc P n` forces
`e P b = e P n` (`embed_eq_iff_raw_code`), so it gives no new information. -/
theorem isoInj_rel_iff_incl {a b : ℕ} :
    (isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b) := by
  show (∃ _ : D.mem (P.X a), (toDprimeUCode P (D.principal (P.mem_X a))).mem (Yc P b)) ↔ _
  simp only [toDprimeUCode, mem_principal]
  have hb : e P b = P.X (eIdx P b) := rfl
  constructor
  · rintro ⟨-, n, hn, -, hsub⟩
    rwa [← hb, (embed_eq_iff_raw_code P b n).mpr hn]
  · intro hsub
    exact ⟨P.mem_X a, b, rfl, (P0 P).mem_X b, hb ▸ hsub⟩

/-- **`isoInj` is computable** relative to `P`/`DprimeUCodePresentation P`: its raw-index relation is
`incl_computable` reindexed by the primitive-recursive `eIdx P` in the second argument. -/
theorem isoInj_isComputableMap : ComputableMap P (DprimeUCodePresentation P) (isoInj P) := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => P.X t.unpair.1 ⊆ P.X (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (P.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoInj P).rel (P.X t.unpair.1) ((DprimeUCodePresentation P).X t.unpair.2) ↔ _
  exact isoInj_rel_iff_incl P

/-- `isoProj ∘ isoInj = I_D` (Theorem 2.7's `toElementMap_ofIso`, both ways, plus `OrderIso.symm_apply_apply`). -/
theorem isoProj_comp_isoInj : (isoProj P).comp (isoInj P) = idMap D := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (isoProj P).toElementMap ((isoInj P).toElementMap x) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
    toElementMap_idMap]

/-- **`isoProj`'s relation at raw indices reduces to a single reindexed inclusion.** `m := eIdx P a`
is always a valid witness (`e P (eIdx P a) = P.X a` by involutivity), and any *other* witness `m`
with `P.X a = e P m` forces `Yc P (eIdx P a) = Yc P m` (via `embed_eq_iff_raw_code` and
`eIdx_involutive`), so it gives no new information. -/
theorem isoProj_rel_iff_incl {b a : ℕ} :
    (isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a) := by
  show (∃ _ : (DprimeUCode P).mem (Yc P b),
      (toDCode P ((DprimeUCode P).principal ⟨b, rfl⟩)).mem (P.X a)) ↔ _
  simp only [toDCode]
  have hea : e P (eIdx P a) = P.X a := by
    show P.X (eIdx P (eIdx P a)) = P.X a
    rw [eIdx_involutive P a]
  constructor
  · rintro ⟨-, m, hm, -, hsub⟩
    have heq : e P (eIdx P a) = e P m := hea.trans hm
    rw [(embed_eq_iff_raw_code P (eIdx P a) m).mp heq]
    exact hsub
  · intro hsub
    exact ⟨⟨b, rfl⟩, eIdx P a, hea.symm, ⟨eIdx P a, rfl⟩, hsub⟩

/-- **`isoProj` is computable** relative to `DprimeUCodePresentation P`/`P`: its raw-index relation is
`DprimeUCodePresentation`'s `incl_computable` reindexed by `eIdx P` in the second argument. -/
theorem isoProj_isComputableMap : ComputableMap (DprimeUCodePresentation P) P (isoProj P) := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => Yc P t.unpair.1 ⊆ Yc P (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((DprimeUCodePresentation P).incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoProj P).rel ((DprimeUCodePresentation P).X t.unpair.1) (P.X t.unpair.2) ↔ _
  exact isoProj_rel_iff_incl P

/-- **`theorem_8_8_b`, strengthened.** For any effectively given `D` (via `P`), there is a
*single* computable projection pair `i : D → U`, `j : U → D` directly (no intermediate isomorphic
copy): compose `isoInj`/`isoProj` (the code-level iso, computable) with `DprimeUCode`'s own projection pair
into `U` (Theorem 8.8(b)(vii), computable). -/
theorem theorem_8_8_b_strong :
    ∃ (i : ApproximableMap D U) (j : ApproximableMap U D),
      j.comp i = idMap D ∧ i.comp j ≤ idMap U ∧
        ComputableMap P UComputablePresentation i ∧
        ComputableMap UComputablePresentation P j := by
  set h := DprimeUCode_subsystem P with hh
  refine ⟨h.inj.comp (isoInj P), (isoProj P).comp h.proj, ?_, ?_, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc h.proj h.inj (isoInj P), h.proj_comp_inj, idMap_comp]
    exact isoProj_comp_isoInj P
  · have heq : (h.inj.comp (isoInj P)).comp ((isoProj P).comp h.proj) = h.inj.comp h.proj := by
      rw [comp_assoc, ← comp_assoc (isoInj P) (isoProj P) h.proj, isoInj_comp_isoProj, idMap_comp]
    rw [heq]
    exact h.inj_comp_proj_le
  · exact comp_isComputable (isoInj_isComputableMap P) (DprimeUCode_inj_isComputableMap P)
  · exact comp_isComputable (DprimeUCode_proj_isComputableMap P) (isoProj_isComputableMap P)

end

end DomainTheory.NeighbourhoodSystems
