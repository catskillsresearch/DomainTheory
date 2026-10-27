module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitX812e
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

theorem foldl_ratMax (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMaxCode (Nat.pair acc x.unpair.2)) z)
      = (l.map decodeRatPair).foldl (fun acc p => max acc p.2) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMaxCode]
    rfl

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem maxSnd_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => max acc p.2) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => max acc q.2) seed = p.2 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total a.2 seed with hle | hle
    · rw [max_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [max_eq_right hle]
      rcases ih a.2 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

end foldl
open Domain.Recursive NeighborhoodSystem

/-- **Every pair of `decodeQPairList (canonCode c)` has both endpoints in `[0, 1]`** — mirrors
`forall_lt_decodeQPairList_canonCode` (nondegeneracy), giving the companion boundedness fact. -/
theorem forall_bounds_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), 0 ≤ p.1 ∧ p.2 ≤ 1 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro p hp
    obtain ⟨p0, -, -, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact ⟨le_sup_right, inf_le_right⟩

/-- `max_i pᵢ.2` over a presenting list, folded with seed `0`. -/
def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0

/-- `min_i pᵢ.1` over a presenting list, folded with seed `1` (safe: every genuine pair has
`p.1 < 1` once bounded, `forall_bounds_decodeQPairList_canonCode`). -/
def listMinFst (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => min acc p.1) 1

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

/-- Bridging `List.foldl` over raw pair-codes (via `ratMinCode`) to `List.foldl` over decoded
pairs (via `min ·.1`), one step at a time. -/
theorem foldl_ratMin (l : List ℕ) (z : ℕ) :
    decodeRat (l.foldl (fun acc x => ratMinCode (Nat.pair acc x.unpair.1)) z)
      = (l.map decodeRatPair).foldl (fun acc p => min acc p.1) (decodeRat z) := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, decodeRat_ratMinCode]
    rfl

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem maxSnd_seed_le (L : List (ℚ × ℚ)) (seed : ℚ) :
    seed ≤ L.foldl (fun acc p => max acc p.2) seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (le_max_left seed a.2).trans (ih (max seed a.2))

end foldl
open Domain.Recursive NeighborhoodSystem

/-- The code-level `listMaxSnd`: fold `ratMaxCode` over `c`'s pair-codes, seeded at `zeroCode`. -/
def listMaxSndCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) 0 zeroCode c

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

theorem listMaxSndCode (c : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode c) = listMaxSnd (decodeQPairList c) := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode listMaxSnd decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMaxCode (Nat.pair acc x.unpair.2)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat.foldl_ratMax, decodeRat_zeroCode]

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem maxSnd_ge (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    p.2 ≤ L.foldl (fun acc q => max acc q.2) seed := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (le_max_right seed p.2).trans (foldl.maxSnd_seed_le l (max seed p.2))
    · exact ih (max seed a.2) hp'

end foldl
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

theorem ge {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : p.2 ≤ listMaxSnd L :=
  foldl.maxSnd_ge L 0 p hp

theorem attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hlb : ∀ p ∈ L, 0 < p.2) :
    ∃ p ∈ L, p.2 = listMaxSnd L := by
  rcases foldl.maxSnd_mem_or_eq_seed L 0 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMaxSnd.ge hp0) (not_le.mpr (hlb p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

end listMaxSnd
open Domain.Recursive NeighborhoodSystem

/-- The code-level `listMinFst`: fold `ratMinCode` over `c`'s pair-codes, seeded at `oneCode`. -/
def listMinFstCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) 0 oneCode c

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

theorem listMinFstCode (c : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.listMinFstCode c) = listMinFst (decodeQPairList c) := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.listMinFstCode listMinFst decodeQPairList
  rw [foldCode_eq']
  have hstep : (fun (acc x : ℕ) =>
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1))
        (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x : ℕ => ratMinCode (Nat.pair acc x.unpair.1)) := by
    funext acc x; simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeRat.foldl_ratMin, decodeRat_oneCode]

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem minFst_le_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed ≤ seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (ih (min seed a.1)).trans (min_le_left seed a.1)

end foldl
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

/-- **`listMaxSnd L` is arbitrarily approached from below by `presentedIntervals L`.** -/
theorem tight {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) {y : ℚ}
    (hy : y < listMaxSnd L) : ∃ x ∈ presentedIntervals L, y < x := by
  have hlb : ∀ p ∈ L, 0 < p.2 := fun p hp => lt_of_le_of_lt (hb p hp).1 (hpos p hp)
  obtain ⟨p, hp, hpeq⟩ := listMaxSnd.attained hne hlb
  rw [← hpeq] at hy
  rcases lt_or_ge y p.1 with hlt | hge
  · exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hpos p hp⟩, hlt⟩
  · exact ⟨(y + p.2) / 2, mem_presentedIntervals.mpr ⟨p, hp, hge.trans (left_lt_add_div_two.mpr hy).le,
      add_div_two_lt_right.mpr hy⟩, left_lt_add_div_two.mpr hy⟩

end listMaxSnd
open Domain.Recursive NeighborhoodSystem

/-- The midpoint code of `canonCode n`'s intrinsic `(min, max)` pair. -/
def splitU2MidCode (n : ℕ) : ℕ :=
  ratMidCode (Nat.pair (listMinFstCode (canonCode n)) (listMaxSndCode (canonCode n)))

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

theorem splitU2MidCode (n : ℕ) :
    decodeRat (_root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode n) =
      (listMinFst (decodeQPairList (canonCode n)) + listMaxSnd (decodeQPairList (canonCode n)))
        / 2 := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode
  rw [decodeRat_ratMidCode', unpair_pair_fst, unpair_pair_snd, decodeRat.listMinFstCode,
    decodeRat.listMaxSndCode]

end decodeRat
namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem minFst_le (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    L.foldl (fun acc q => min acc q.1) seed ≤ p.1 := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (foldl.minFst_le_seed l (min seed p.1)).trans (min_le_right seed p.1)
    · exact ih (min seed a.1) hp'

end foldl
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

theorem le {L : List (ℚ × ℚ)} {p : ℚ × ℚ} (hp : p ∈ L) : listMinFst L ≤ p.1 :=
  foldl.minFst_le L 1 p hp

end listMinFst
namespace splitU2
open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ`'s intrinsic minimum is strictly below its intrinsic maximum**, via any single
witnessing pair of `canonCode n`'s presenting list (nonempty, `forall_lt_...`). -/
theorem min_lt_max (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < listMaxSnd (decodeQPairList (canonCode n)) := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (decodeQPairList_canonCode_ne_nil n)
  exact lt_of_le_of_lt (listMinFst.le hp)
    (lt_of_lt_of_le (forall_lt_decodeQPairList_canonCode n p hp) (listMaxSnd.ge hp))

theorem mid_lt_max (n : ℕ) :
    decodeRat (splitU2MidCode n) < listMaxSnd (decodeQPairList (canonCode n)) := by
  rw [decodeRat.splitU2MidCode]; exact add_div_two_lt_right.mpr (splitU2.min_lt_max n)

theorem min_lt_mid (n : ℕ) :
    listMinFst (decodeQPairList (canonCode n)) < decodeRat (splitU2MidCode n) := by
  rw [decodeRat.splitU2MidCode]; exact left_lt_add_div_two.mpr (splitU2.min_lt_max n)

end splitU2
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

/-- **`listMaxSnd L` strictly upper-bounds `presentedIntervals L`.** -/
theorem upper_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    x < listMaxSnd L := by
  obtain ⟨p, hp, -, hx2⟩ := mem_presentedIntervals.mp hx
  exact hx2.trans_le (listMaxSnd.ge hp)

end listMaxSnd
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

/-- **`listMinFst L` lower-bounds `presentedIntervals L`.** -/
theorem lower_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    listMinFst L ≤ x := by
  obtain ⟨p, hp, hx1, -⟩ := _root_.DomainTheory.NeighbourhoodSystems.mem_presentedIntervals.mp hx
  exact (listMinFst.le hp).trans hx1

end listMinFst
open Domain.Recursive NeighborhoodSystem

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
intrinsic `(min, max)`. -/
def splitU2Left (n : ℕ) : ℕ := clipLtListCode (splitU2MidCode n) (canonCode n)

namespace foldl
open Domain.Recursive NeighborhoodSystem

theorem minFst_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => min acc q.1) seed = p.1 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total seed a.1 with hle | hle
    · rw [min_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [min_eq_right hle]
      rcases ih a.1 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

end foldl
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

theorem attained {L : List (ℚ × ℚ)} (hne : L ≠ []) (hub : ∀ p ∈ L, p.1 < 1) :
    ∃ p ∈ L, p.1 = listMinFst L := by
  rcases foldl.minFst_mem_or_eq_seed L 1 with h1 | ⟨p, hp, h1⟩
  · obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil L hne
    exact absurd (h1 ▸ listMinFst.le hp0) (not_le.mpr (hub p0 hp0))
  · exact ⟨p, hp, h1.symm⟩

end listMinFst
namespace listMaxSnd
open Domain.Recursive NeighborhoodSystem

/-- **`listMaxSnd` is a well-defined function of the presented set alone.** -/
theorem congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMaxSnd L1 = listMaxSnd L2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd.tight hne2 hpos2 hb2 hlt
    have hx1 : x ∈ presentedIntervals L1 := heq.symm ▸ hx
    exact absurd (listMaxSnd.upper_bound hx1) (not_lt.mpr hyx.le)
  · obtain ⟨x, hx, hyx⟩ := listMaxSnd.tight hne1 hpos1 hb1 hlt
    have hx2 : x ∈ presentedIntervals L2 := heq ▸ hx
    exact absurd (listMaxSnd.upper_bound hx2) (not_lt.mpr hyx.le)

end listMaxSnd
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

/-- **`listMinFst L` is the genuine minimum of `presentedIntervals L`** (membership half). -/
theorem mem_presentedIntervals {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) :
    listMinFst L ∈ presentedIntervals L := by
  have hub : ∀ p ∈ L, p.1 < 1 := fun p hp => (hpos p hp).trans_le (hb p hp).2
  obtain ⟨p, hp, hpeq⟩ := listMinFst.attained hne hub
  exact _root_.DomainTheory.NeighbourhoodSystems.mem_presentedIntervals.mpr ⟨p, hp, hpeq.le, hpeq ▸ hpos p hp⟩

/-- **`listMinFst` is a well-defined function of the presented set alone**, mirroring
`MinLevel.lean`'s `minLevel_unique` for `V`: two (nonempty, nondegenerate, `[0,1]`-bounded)
presenting lists of the *same* set have the same `listMinFst`. -/
theorem congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMinFst L1 = listMinFst L2 := by
  have hm1 : listMinFst L1 ∈ presentedIntervals L2 :=
    heq ▸ listMinFst.mem_presentedIntervals hne1 hpos1 hb1
  have hm2 : listMinFst L2 ∈ presentedIntervals L1 :=
    heq ▸ listMinFst.mem_presentedIntervals hne2 hpos2 hb2
  exact le_antisymm (listMinFst.lower_bound hm2) (listMinFst.lower_bound hm1)

end listMinFst
open Domain.Recursive NeighborhoodSystem

/-- **`splitU2Left`/`splitU2Right`'s midpoint depends only on `UX n` as a set** — the key lemma
that `SplitU.lean`'s `splitULeft`/`splitURight` lack, via `listMinFst.congr`/`listMaxSnd.congr`. -/
theorem splitU2MidCode_congr {n n' : ℕ} (h : UX n = UX n') :
    decodeRat (splitU2MidCode n) = decodeRat (splitU2MidCode n') := by
  have heqP : presentedIntervals (decodeQPairList (canonCode n))
      = presentedIntervals (decodeQPairList (canonCode n')) := h
  have hminEq := listMinFst.congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  have hmaxEq := listMaxSnd.congr (decodeQPairList_canonCode_ne_nil n)
    (decodeQPairList_canonCode_ne_nil n') (forall_lt_decodeQPairList_canonCode n)
    (forall_bounds_decodeQPairList_canonCode n) (forall_lt_decodeQPairList_canonCode n')
    (forall_bounds_decodeQPairList_canonCode n') heqP
  rw [decodeRat.splitU2MidCode, decodeRat.splitU2MidCode, hminEq, hmaxEq]

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitU2Right (n : ℕ) : ℕ := clipGeListCode (splitU2MidCode n) (canonCode n)

theorem UX_splitU2Right (n : ℕ) :
    UX (splitU2Right n) = UX n ∩ Set.Ici (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Right n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxgt⟩ := listMaxSnd.tight (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
        (splitU2.mid_lt_max n)
      exact ⟨x, hx, hxgt.le⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Right n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

/-- **`splitU2Right`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Right_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Right n) = UX (splitU2Right n') := by
  rw [UX_splitU2Right, UX_splitU2Right, h, splitU2MidCode_congr h]

theorem UX_splitU2Left (n : ℕ) :
    UX (splitU2Left n) = UX n ∩ Set.Iio (decodeRat (splitU2MidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitU2Left n))) := by
    show U.mem
      (presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitU2MidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨listMinFst (decodeQPairList (canonCode n)), ?_, splitU2.min_lt_mid n⟩
      exact listMinFst.mem_presentedIntervals (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Left n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

namespace splitU2
open Domain.Recursive NeighborhoodSystem

/-- **Disjointness**: `splitU2Left`/`splitU2Right` cover disjoint pieces. -/
theorem disjoint (n : ℕ) : UX (splitU2Left n) ∩ UX (splitU2Right n) = ∅ := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

/-- **Covering**: `splitU2Left`/`splitU2Right` reunite to `Xₙ`. -/
theorem union (n : ℕ) : UX (splitU2Left n) ∪ UX (splitU2Right n) = UX n := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitU2MidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

end splitU2
open Domain.Recursive NeighborhoodSystem

/-- **`splitU2Left`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Left_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Left n) = UX (splitU2Left n') := by
  rw [UX_splitU2Left, UX_splitU2Left, h, splitU2MidCode_congr h]

theorem zero_le_listMaxSnd (L : List (ℚ × ℚ)) : 0 ≤ listMaxSnd L := foldl.maxSnd_seed_le L 0

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem listMaxSndCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.listMaxSndCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) :=
    (primrec_ratMaxCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const zeroCode) primrec_id).of_eq
    fun _ => rfl

theorem listMinFstCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.listMinFstCode := by
  have hstp : Nat.Primrec
      (fun t : ℕ => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) :=
    (primrec_ratMinCode.comp ((Nat.Primrec.left.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.left))).of_eq fun _ => rfl
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) (Nat.Primrec.const oneCode) primrec_id).of_eq
    fun _ => rfl

theorem splitU2MidCode : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode :=
  (primrec_ratMidCode.comp
    ((primrec.listMinFstCode.comp primrec_canonCode).pair
      (primrec.listMaxSndCode.comp primrec_canonCode))).of_eq fun n => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2MidCode]

theorem splitU2Left : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2Left :=
  (primrec_clipLtListCode.comp (primrec.splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2Left, unpair_pair_fst, unpair_pair_snd]

theorem splitU2Right : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.splitU2Right :=
  (primrec_clipGeListCode.comp (primrec.splitU2MidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [_root_.DomainTheory.NeighbourhoodSystems.splitU2Right, unpair_pair_fst, unpair_pair_snd]

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **`U`'s computable canonical bisection, packaged as a `ComputableBisection`** — the missing
`(f)`-side prerequisite, fixing `SplitU.lean`'s `left_congr`/`right_congr` gap (see the module
docstring). -/
def UBisection2 : ComputableBisection UComputablePresentation where
  left := splitU2Left
  right := splitU2Right
  left_primrec := primrec.splitU2Left
  right_primrec := primrec.splitU2Right
  disjoint := splitU2.disjoint
  union := splitU2.union
  left_congr := fun _ _ h => splitU2Left_congr h
  right_congr := fun _ _ h => splitU2Right_congr h

namespace listMinFst
open Domain.Recursive NeighborhoodSystem

theorem le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl.minFst_le_seed L 1

end listMinFst
open Domain.Recursive NeighborhoodSystem

/-- The difference index: `canonIdx` of the raw difference code `VdiffRaw`. -/
def Vdiff (n m : ℕ) : ℕ := canonIdx (VdiffRaw n m)

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **The "same level" set-difference formula**, mirroring `Exercise812.lean`'s
`levelSet.inter_same_level` exactly (`&&&` becomes the "and-not" combinator `a ^^^ (a &&& b)`,
via `testBit.xor_and_self`). -/
theorem diff_same_level (k m₁ m₂ : ℕ) :
    levelSet k m₁ \ levelSet k m₂ = levelSet k (m₁ ^^^ (m₁ &&& m₂)) := by
  ext n; simp [levelSet]

/-- **Computable version of `levelSet.diff_same_level`, upsampled to a common level** — mirrors
`levelSet.myInter` exactly, substituting `myAndNot` for `myLand`. -/
theorem myDiff (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 \ levelSet k2 m2
      = levelSet (max k1 k2) (myAndNot (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) (m := m1),
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) (m := m2)]
  rw [levelSet.diff_same_level, myAndNot_eq]

/-- **`VdiffRaw` realizes `VX n \ VX m`** at the `levelSet` level (unconditionally). -/
theorem VdiffRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VdiffRaw n m).unpair.2 = VX n \ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myDiff (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
namespace Vdiff
open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, mirroring
`Vcons_iff_nonempty_inter`. -/
theorem iff_nonempty (n m : ℕ) :
    (∃ k, VX k = VX n \ VX m) ↔ (VX n \ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact VX_nonempty k
  · intro hne
    rw [← levelSet.VdiffRaw] at hne
    have hVmem : V.mem (VX n \ VX m) := by
      rw [← levelSet.VdiffRaw]
      exact ⟨(VdiffRaw n m).unpair.1, (VdiffRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, hk⟩

theorem spec {n m : ℕ} (h : ∃ k, VX k = VX n \ VX m) : VX (Vdiff n m) = VX n \ VX m := by
  have hne : (levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VdiffRaw]; obtain ⟨k, hk⟩ := h; rw [← hk]; exact VX_nonempty k
  unfold Vdiff
  rw [VX_canonIdx]
  show levelSet (canonIdx (VdiffRaw n m)).unpair.1 (canonIdx (VdiffRaw n m)).unpair.2 = VX n \ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VdiffRaw]

end Vdiff
namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem lowXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.lowXor t.unpair.1 t.unpair.2) :=
  (primrec_mod2.comp
    (primrec_add₂ (primrec_mod2.comp Nat.Primrec.left) (primrec_mod2.comp Nat.Primrec.right))).of_eq
    fun _ => rfl

theorem xorStep : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => _root_.DomainTheory.NeighbourhoodSystems.lowXor s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec.lowXor.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

theorem myXor : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myXor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.xorStep w.unpair.2.unpair.2) :=
    primrec.xorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

theorem myAndNot : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.myAndNot t.unpair.1 t.unpair.2) := by
  have hland : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myLand t.unpair.1 t.unpair.2) := primrec.myLand
  exact (primrec.myXor.comp (Nat.Primrec.left.pair hland)).of_eq fun t => by
    simp only [_root_.DomainTheory.NeighbourhoodSystems.myAndNot, unpair_pair_fst, unpair_pair_snd]

theorem VdiffRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VdiffRaw t.unpair.1 t.unpair.2) := by
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
  have handnot : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.myAndNot
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec.myAndNot.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair handnot).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`\`, for `V`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable. -/
theorem V_diff_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n \ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VdiffRaw t.unpair.1 t.unpair.2) := primrec.VdiffRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec.myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty.le_one (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vdiff.iff_nonempty, ← levelSet.VdiffRaw,
      myLevelSetNonempty.eq_one_iff]

namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem Vdiff : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vdiff t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VdiffRaw).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec.Vdiff
  diffIdx_spec := Vdiff.spec
  diff_computable := V_diff_computable

/-- **`splitX812f`: the exercise's literal target split**, `V` as prober against `U`'s canonical
bisection (`UBisection2`). -/
noncomputable def splitX812f : Set ℕ → Set ℚ → Set ℕ → Set ℚ × Set ℚ :=
  ComputableBisection.splitFromBisection VComputablePresentation V_isComputableDiff UBisection2
    U_noMinimal

namespace isComputableSplit
open Domain.Recursive NeighborhoodSystem

/-- **Exercise 8.12(f), completed in full**: `splitX812f` satisfies `IsComputableSplit`, the
mirror image of `Exercise812eD.lean`'s `isComputableSplit.812e`. `noncomputable def`, not
`theorem` — `IsComputableSplit` is a data-carrying structure (its `posIdx`/`negIdx` fields are
`ℕ`-valued functions), exactly as `isComputableSplit.812e` itself. -/
noncomputable def «812f» :
    IsComputableSplit VComputablePresentation UComputablePresentation splitX812f :=
  ComputableBisection.isComputableSplit.ofBisection VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed

end isComputableSplit
open Domain.Recursive NeighborhoodSystem

/-- The union index: list-concatenate the two canonicalized presenting lists. `UX` re-canonicalizes
on lookup, so no further canonicalization of the inputs is needed here (mirrors `Udiff`). -/
def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)

/-- The union index: `canonIdx` of the raw union code `VunionRaw`. -/
def Vunion (n m : ℕ) : ℕ := canonIdx (VunionRaw n m)

/-- `hX0`: index `0` presents `U`'s master neighbourhood. `decodeQPairList 0 = []`
(`decodeList_zero`), so `canonList` falls back to its `[(0,1)]` branch, which presents
`U.master` exactly as in `U_mem_presentedIntervals_canonList`. -/
theorem UX_zero : UX 0 = U.master := by
  rw [UX_eq]
  have hL : decodeQPairList 0 = [] := by
    unfold decodeQPairList; rw [decodeList_zero]; rfl
  rw [hL, canonList_eq_of_filter_eq_nil (by simp), presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]
  rfl

namespace Uunion
open Domain.Recursive NeighborhoodSystem

theorem primrec : Nat.Primrec (fun t : ℕ => Uunion t.unpair.1 t.unpair.2) := by
  unfold Uunion
  exact (primrec_appendListCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

end Uunion
open Domain.Recursive NeighborhoodSystem

/-- `hD₁mne` for `V`: the master neighbourhood `V.master = Set.univ` is non-empty. -/
theorem V_master_nonempty : V.master.Nonempty := Set.univ_nonempty

/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

namespace Uunion
open Domain.Recursive NeighborhoodSystem

/-- **`Uunion` realizes set union at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — concatenating presenting lists always presents the union, no consistency case
split needed (the one respect in which `∪` is even simpler than `\`'s `Udiff.eq_diff`). -/
theorem eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals_append]
  rfl

end Uunion
section
open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)


namespace splitFromBisection
/-- **`splitFromBisection` satisfies `SplitSpec'`**, completing the concrete-construction half of
`8.12(g)(3)`. Needs one extra hypothesis beyond `isComputableSplit.ofBisection`'s own,
`hQne : ∀ j, Q.X j ≠ ∅` — true for both `U`/`V` (every `ComputablePresentation` index is `mem`-
genuine, and both systems' `mem` structurally excludes `∅`; see `Exercise812.lean` line 199/
`Definition87.lean` line 96) but not derivable from `ComputableBisection`'s abstract fields alone
(nothing there stops `Q.X (B.left m)`, say, from being `∅` in general — only used in the "neither
decider fires" branch, to show the bisection's two halves are each individually `≠ ∅`, matching that
branch's `A ∩ Xn ≠ ∅ ↔ .1 ≠ ∅`/`A \ Xn ≠ ∅ ↔ .2 ≠ ∅` obligations). The two decider-fires branches
need no such hypothesis at all — `.1`/`.2` there are literally `∅`/`B'`, and the requisite `↔`s
reduce to `hAB` via the algebraic facts `A ∩ Xn = ∅ → A \ Xn = A` (resp. `A \ Xn = ∅ → A ∩ Xn = A`).
The "not presented" branch reduces to exactly `splitChoice'_isSplitSpec` (`Exercise812c.lean`),
verbatim. -/
theorem isSplitSpec' (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hQne : ∀ j, Q.X j ≠ ∅) :
    SplitSpec' W (splitFromBisection P hDiff B hWnomin) := by
  intro A B' hAB hBW Xn
  by_cases h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k
  · obtain ⟨n, m, k, rfl, rfl, rfl⟩ := h
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k]
    by_cases h1 : emptyInterDec P (Nat.pair n k) = 1
    · have hInterEmpty : P.X n ∩ P.X k = ∅ := (emptyInterDec.eq_one_iff P hpos hnomin n k).mp h1
      have hdiffEq : P.X n \ P.X k = P.X n := by
        ext x
        simp only [Set.mem_sdiff]
        exact ⟨fun hx => hx.1, fun hx =>
          ⟨hx, fun hxk => Set.eq_empty_iff_forall_notMem.mp hInterEmpty x ⟨hx, hxk⟩⟩⟩
      rw [ite_eq_left h1]
      refine ⟨Or.inl rfl, hBW, iff_of_true hInterEmpty rfl, ?_, Set.empty_union _,
        Set.empty_inter _⟩
      rw [hdiffEq]; exact hAB
    · by_cases h2 : emptyDiffDec P hDiff (Nat.pair n k) = 1
      · have hDiffEmpty : P.X n \ P.X k = ∅ :=
          (emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mp h2
        have hInterEq : P.X n ∩ P.X k = P.X n := by
          ext x
          simp only [Set.mem_inter_iff]
          refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
          by_contra hxk
          exact Set.eq_empty_iff_forall_notMem.mp hDiffEmpty x ⟨hx, hxk⟩
        rw [ite_eq_right h1, ite_eq_left h2]
        refine ⟨hBW, Or.inl rfl, ?_, iff_of_true hDiffEmpty rfl, Set.union_empty _,
          Set.inter_empty _⟩
        rw [hInterEq]; exact hAB
      · have h1' : P.X n ∩ P.X k ≠ ∅ :=
          fun he => h1 ((emptyInterDec.eq_one_iff P hpos hnomin n k).mpr he)
        have h2' : P.X n \ P.X k ≠ ∅ :=
          fun he => h2 ((emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k).mpr he)
        rw [ite_eq_right h1, ite_eq_right h2]
        exact ⟨Or.inr (Q.mem_X _), Or.inr (Q.mem_X _), iff_of_false h1' (hQne _),
          iff_of_false h2' (hQne _), B.union m, B.disjoint m⟩
  · unfold splitFromBisection
    rw [dite_eq_right h]
    exact splitChoice'_isSplitSpec W hWnomin hAB hBW Xn

end splitFromBisection
end ComputableBisection
end

open Domain.Recursive NeighborhoodSystem

/-- **`8.12(g)(3)`, `V`-as-prober half**: `splitX812f` also satisfies `SplitSpec'`, the mirror
image of `Exercise812eD.lean`'s `hxSplit812e`. The extra hypothesis it needs, `∀ j, UX j ≠ ∅`, is
immediate from `U_mem_UX`/`U.mem`'s own `X.Nonempty` conjunct (`Definition87.lean` line 96). -/
theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection.isSplitSpec' VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)

namespace Uunion
open Domain.Recursive NeighborhoodSystem

/-- **`Uunion n m` genuinely indexes `UX n ∪ UX m`** — mirrors `Udiff.spec`'s shape exactly, but the
hypothesis is never used (the union is already unconditionally genuine, `U_union_mem`): the raw
`appendListCode` output is already a genuine `U`-neighbourhood, so re-canonicalizing it (`canonCode`'s
own lookup, `UX`'s definition) is a no-op (`canonList_fixed`). -/
theorem spec {n m : ℕ} (_ : ∃ k, UX k = UX n ∪ UX m) : UX (Uunion n m) = UX n ∪ UX m := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (Uunion n m))) := by
    rw [Uunion.eq_union]; exact U_union_UX_mem n m
  show presentedIntervals (decodeQPairList (canonCode (Uunion n m))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL, Uunion.eq_union]

end Uunion
open Domain.Recursive NeighborhoodSystem

/-- **`8.12(g)(3)`, `U`-as-prober half**: `splitX812e` also satisfies `SplitSpec'` — completing the
concrete-construction half of `8.12(g)(3)` left open by `Exercise812e.lean`'s generic
`splitFromBisection.isSplitSpec'`. The extra hypothesis it needs, `∀ j, VX j ≠ ∅`, is immediate:
every `VX j` is `V.mem`-genuine (`VComputablePresentation.mem_X`) and `V.mem` structurally excludes
`∅` (`V.mem X := ∃ k m, X = levelSet k m ∧ X.Nonempty`, `Exercise812.lean` line 199). -/
theorem hxSplit812e : SplitSpec' V splitX812e :=
  ComputableBisection.splitFromBisection.isSplitSpec' UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed (fun j => (VX_nonempty j).ne_empty)

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `𝒰` — via `U_surj_UX` on
`U_union_UX_mem` (mirroring `U_diff_iff_nonempty`'s use of `U_surj_UX`, but unconditional). -/
theorem U_union_exists (n m : ℕ) : ∃ k, UX k = UX n ∪ UX m := U_surj_UX (U_union_UX_mem n m)

/-- **7.1(i)-for-`∪`, for `𝒰`**: trivially recursively decidable (the always-`1` constant), since
`U_union_exists` shows the underlying predicate is unconditionally `True`. -/
theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩

/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion.primrec
  unionIdx_spec := Uunion.spec
  union_computable := U_union_computable

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet.union_same_level` at differing levels** — the bitwise-`OR`
analogue of `levelSet.myInter`, mirroring its proof verbatim with `myLor`/`Nat.testBit_or` in place
of `myLand`/`Nat.testBit_and`. -/
theorem myUnion (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 ∪ levelSet k2 m2
      = levelSet (max k1 k2) (myLor (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k1 (max k1 k2) m1) (_root_.DomainTheory.NeighbourhoodSystems.myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet.myUpsample (Nat.le_max_left k1 k2) m1,
    ← levelSet.myUpsample (Nat.le_max_right k1 k2) m2]
  rw [levelSet.union_same_level, myLor_eq_lor]

/-- **`VunionRaw` realizes `VX n ∪ VX m`** at the `levelSet` level (unconditionally). -/
theorem VunionRaw (n m : ℕ) :
    levelSet (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.VunionRaw n m).unpair.2 = VX n ∪ VX m := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.VunionRaw
  rw [unpair_pair_fst, unpair_pair_snd]
  exact (levelSet.myUnion (canonIdx n).unpair.1 (canonIdx n).unpair.2
    (canonIdx m).unpair.1 (canonIdx m).unpair.2).symm

end levelSet
namespace Vunion
open Domain.Recursive NeighborhoodSystem

/-- **`Vunion n m` genuinely indexes `VX n ∪ VX m`**, unconditionally — `VunionRaw n m` is already
non-empty (both `VX n`, `VX m` are non-empty, `VX_nonempty`, and a union of a non-empty set with
anything is non-empty), so `canonIdx` is a no-op on it (`canonIdx.eq_self_of_nonempty`), mirroring
`Vinter_spec`'s shape but with the hypothesis discharged internally rather than assumed. -/
theorem spec (n m : ℕ) : VX (Vunion n m) = VX n ∪ VX m := by
  have hne : (levelSet (VunionRaw n m).unpair.1 (VunionRaw n m).unpair.2).Nonempty := by
    rw [levelSet.VunionRaw]; exact (VX_nonempty n).mono Set.subset_union_left
  unfold Vunion
  rw [VX_canonIdx]
  show levelSet (canonIdx (VunionRaw n m)).unpair.1 (canonIdx (VunionRaw n m)).unpair.2 = VX n ∪ VX m
  rw [canonIdx.eq_self_of_nonempty hne, levelSet.VunionRaw]

/-- `Vunion.spec`, repackaged to accept (and discard) `IsComputableUnion`'s hypothesis. -/
theorem spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion.spec n m

end Vunion
open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion.spec n m⟩

/-- **7.1(i)-for-`∪`, for `V`**: trivially recursively decidable (the always-`1` constant). -/
theorem V_union_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n ∪ VX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (V_union_exists t.unpair.1 t.unpair.2) rfl⟩

namespace levelSet
open Domain.Recursive NeighborhoodSystem

/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

end levelSet
open Domain.Recursive NeighborhoodSystem

/-- `hY0`: index `0` presents `V`'s master neighbourhood. `Nat.unpair 0 = (0, 0)` and
`levelSet 0 0 = ∅`, so `canonIdx 0` falls back to `VmasterIdx = Nat.pair 0 1`
(`canonIdx.eq_master_of_empty`), whose `VX`-image is `V.master` (`VX_VmasterIdx`). -/
theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx.eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet.zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx

set_option linter.unusedVariables false

theorem example_812_e_d : @DomainTheory.NeighbourhoodSystems.SplitSpec' Rat Nat DomainTheory.NeighbourhoodSystems.V
  DomainTheory.NeighbourhoodSystems.splitX812e :=
  @DomainTheory.NeighbourhoodSystems.hxSplit812e

theorem example_812_f : @DomainTheory.NeighbourhoodSystems.SplitSpec' Nat Rat DomainTheory.NeighbourhoodSystems.U
  DomainTheory.NeighbourhoodSystems.splitX812f :=
  @DomainTheory.NeighbourhoodSystems.hySplit812f

theorem example_812_g1a : @Eq (Set Rat) (DomainTheory.NeighbourhoodSystems.UX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Rat DomainTheory.NeighbourhoodSystems.U) :=
  DomainTheory.NeighbourhoodSystems.UX_zero

theorem example_812_g1b : @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master Nat DomainTheory.NeighbourhoodSystems.V) :=
  DomainTheory.NeighbourhoodSystems.VX_zero

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion.spec'


namespace primrec
open Domain.Recursive NeighborhoodSystem

theorem VunionRaw : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.VunionRaw t.unpair.1 t.unpair.2) := by
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
  have hlor : Nat.Primrec (fun t : ℕ => myLor
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.myUpsample (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1
        (max (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.1).unpair.1 (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.1) (_root_.DomainTheory.NeighbourhoodSystems.canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myLor.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair hlor).of_eq fun _ => rfl

theorem Vunion : Nat.Primrec (fun t => _root_.DomainTheory.NeighbourhoodSystems.Vunion t.unpair.1 t.unpair.2) :=
  (primrec.canonIdx.comp primrec.VunionRaw).of_eq fun _ => rfl

end primrec
open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `∪`.** -/
def V_isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec.Vunion
  unionIdx_spec := Vunion.spec'
  union_computable := V_union_computable

open Domain.Recursive NeighborhoodSystem Exercise718

/-- **Exercise 8.12, completed in full**: `U` and `V` are effectively isomorphic
neighbourhood systems. -/
noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V_isComputableDiff splitX812e isComputableSplit.«812e» splitX812f isComputableSplit.«812f»
    U_isPositive U_diffClosed U_noMinimal hxSplit812e V_isPositive V_diffClosed V_noMinimal
    hySplit812f U_master_nonempty V_master_nonempty U_isComputableUnion V_isComputableUnion UX_zero
    VX_zero

end DomainTheory.NeighbourhoodSystems
end
