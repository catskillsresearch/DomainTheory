module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU

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

def listMaxSnd (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => max acc p.2) 0

def listMinFst (L : List (ℚ × ℚ)) : ℚ := L.foldl (fun acc p => min acc p.1) 1

namespace decodeRat
open Domain.Recursive NeighborhoodSystem

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

theorem tight {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) {y : ℚ}
    (hy : y < listMaxSnd L) : ∃ x ∈ presentedIntervals L, y < x := by
  have hlb : ∀ p ∈ L, 0 < p.2 := fun p hp => lt_of_le_of_lt (hb p hp).1 (hpos p hp)
  obtain ⟨p, hp, hpeq⟩ := listMaxSnd.attained hne hlb
  rw [← hpeq] at hy
  rcases lt_or_ge y p.1 with hlt | hge
  · exact ⟨p.1, presentedIntervals.mem.mpr ⟨p, hp, le_refl _, hpos p hp⟩, hlt⟩
  · exact ⟨(y + p.2) / 2, presentedIntervals.mem.mpr ⟨p, hp, hge.trans (left_lt_add_div_two.mpr hy).le,
      add_div_two_lt_right.mpr hy⟩, left_lt_add_div_two.mpr hy⟩

end listMaxSnd
open Domain.Recursive NeighborhoodSystem

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

theorem upper_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    x < listMaxSnd L := by
  obtain ⟨p, hp, -, hx2⟩ := presentedIntervals.mem.mp hx
  exact hx2.trans_le (listMaxSnd.ge hp)

end listMaxSnd
namespace listMinFst
open Domain.Recursive NeighborhoodSystem

theorem lower_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    listMinFst L ≤ x := by
  obtain ⟨p, hp, hx1, -⟩ := _root_.DomainTheory.NeighbourhoodSystems.presentedIntervals.mem.mp hx
  exact (listMinFst.le hp).trans hx1

end listMinFst
open Domain.Recursive NeighborhoodSystem

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

theorem presentedIntervals.mem {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) :
    listMinFst L ∈ presentedIntervals L := by
  have hub : ∀ p ∈ L, p.1 < 1 := fun p hp => (hpos p hp).trans_le (hb p hp).2
  obtain ⟨p, hp, hpeq⟩ := listMinFst.attained hne hub
  exact _root_.DomainTheory.NeighbourhoodSystems.presentedIntervals.mem.mpr ⟨p, hp, hpeq.le, hpeq ▸ hpos p hp⟩

theorem congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMinFst L1 = listMinFst L2 := by
  have hm1 : listMinFst L1 ∈ presentedIntervals L2 :=
    heq ▸ listMinFst.presentedIntervals.mem hne1 hpos1 hb1
  have hm2 : listMinFst L2 ∈ presentedIntervals L1 :=
    heq ▸ listMinFst.presentedIntervals.mem hne2 hpos2 hb2
  exact le_antisymm (listMinFst.lower_bound hm2) (listMinFst.lower_bound hm1)

end listMinFst
open Domain.Recursive NeighborhoodSystem

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
      exact listMinFst.presentedIntervals.mem (decodeQPairList_canonCode_ne_nil n)
        (forall_lt_decodeQPairList_canonCode n) (forall_bounds_decodeQPairList_canonCode n)
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitU2Left n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitU2MidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

namespace splitU2
open Domain.Recursive NeighborhoodSystem

theorem disjoint (n : ℕ) : UX (splitU2Left n) ∩ UX (splitU2Right n) = ∅ := by
  rw [UX_splitU2Left, UX_splitU2Right]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

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

namespace listMinFst
open Domain.Recursive NeighborhoodSystem

theorem le_one (L : List (ℚ × ℚ)) : listMinFst L ≤ 1 := foldl.minFst_le_seed L 1

end listMinFst

end DomainTheory.NeighbourhoodSystems
