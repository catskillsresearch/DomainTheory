module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

def presentedIntervals (L : List (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ L, Set.Ico p.1 p.2

def clip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

def clipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

def clipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

def combineIntervals (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  L1.flatMap (fun p => L2.map (fun q => (p.1 ⊔ q.1, p.2 ⊓ q.2)))

theorem Ico_diff_Ico (a b c d : ℚ) :
    Set.Ico a b \ Set.Ico c d = Set.Ico a (b ⊓ c) ∪ Set.Ico (a ⊔ d) b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_union, lt_inf_iff, sup_le_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hcd⟩
    rcases lt_or_ge x c with hc | hc
    · exact Or.inl ⟨ha, hb, hc⟩
    · rcases lt_or_ge x d with hd | hd
      · exact absurd ⟨hc, hd⟩ hcd
      · exact Or.inr ⟨⟨ha, hd⟩, hb⟩
  · rintro (⟨ha, hb, hc⟩ | ⟨⟨ha, hd⟩, hb⟩)
    · exact ⟨⟨ha, hb⟩, fun ⟨hc', _⟩ => absurd hc' (not_le.mpr hc)⟩
    · exact ⟨⟨ha, hb⟩, fun ⟨_, hd'⟩ => absurd hd' (not_lt.mpr hd)⟩

def diffOneList (p q : ℚ × ℚ) : List (ℚ × ℚ) := [(p.1, p.2 ⊓ q.1), (p.1 ⊔ q.2, p.2)]

def diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) : List (ℚ × ℚ) :=
  L.flatMap (fun p => diffOneList p q)

def diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L2.foldl diffSingleList [p]

def diffLists (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L1.flatMap (fun p => diffAllList p L2)

namespace presentedIntervals

@[simp] theorem mem {L : List (ℚ × ℚ)} {x : ℚ} :
    x ∈ presentedIntervals L ↔ ∃ p ∈ L, p.1 ≤ x ∧ x < p.2 := by
  simp only [presentedIntervals, Set.mem_iUnion, Set.mem_Ico, exists_prop]

@[simp] theorem nil : presentedIntervals ([] : List (ℚ × ℚ)) = ∅ := by
  ext x; simp

theorem cons (p : ℚ × ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (p :: L) = Set.Ico p.1 p.2 ∪ presentedIntervals L := by
  ext x; simp [Set.mem_Ico, or_and_right, exists_or]

theorem append (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (L1 ++ L2) = presentedIntervals L1 ∪ presentedIntervals L2 := by
  induction L1 with
  | nil => simp
  | cons p L1 ih => simp [List.cons_append, cons, ih, Set.union_assoc]

theorem congr {L1 L2 : List (ℚ × ℚ)} (h : ∀ p, p ∈ L1 ↔ p ∈ L2) :
    presentedIntervals L1 = presentedIntervals L2 := by
  ext x
  simp only [mem]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mp hp, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mpr hp, h1, h2⟩

theorem inter (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals L1 ∩ presentedIntervals L2 = presentedIntervals (combineIntervals L1 L2) := by
  ext x
  simp only [mem, combineIntervals, List.mem_flatMap, List.mem_map,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨p, hp, hxp1, hxp2⟩, ⟨q, hq, hxq1, hxq2⟩⟩
    exact ⟨(p.1 ⊔ q.1, p.2 ⊓ q.2), ⟨p, hp, q, hq, rfl⟩, sup_le hxp1 hxq1, lt_inf_iff.mpr ⟨hxp2, hxq2⟩⟩
  · rintro ⟨r, ⟨p, hp, q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨p, hp, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      ⟨q, hq, le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩⟩

theorem diffOneList (p q : ℚ × ℚ) :
    presentedIntervals (_root_.DomainTheory.NeighbourhoodSystems.diffOneList p q) =
      Set.Ico p.1 p.2 \ Set.Ico q.1 q.2 := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.diffOneList
  rw [cons, cons, nil, Set.union_empty]
  exact (Ico_diff_Ico p.1 p.2 q.1 q.2).symm

theorem diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) :
    presentedIntervals (_root_.DomainTheory.NeighbourhoodSystems.diffSingleList L q) =
      presentedIntervals L \ Set.Ico q.1 q.2 := by
  induction L with
  | nil => simp [_root_.DomainTheory.NeighbourhoodSystems.diffSingleList]
  | cons a l ih =>
    rw [show _root_.DomainTheory.NeighbourhoodSystems.diffSingleList (a :: l) q =
        _root_.DomainTheory.NeighbourhoodSystems.diffOneList a q ++
          _root_.DomainTheory.NeighbourhoodSystems.diffSingleList l q from rfl,
      append, presentedIntervals.diffOneList, ih, cons, Set.union_sdiff_distrib]

theorem foldl_diffSingleList (L2 : List (ℚ × ℚ)) :
    ∀ acc : List (ℚ × ℚ),
      presentedIntervals (L2.foldl _root_.DomainTheory.NeighbourhoodSystems.diffSingleList acc) =
        presentedIntervals acc \ presentedIntervals L2 := by
  induction L2 with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons,
      ih (_root_.DomainTheory.NeighbourhoodSystems.diffSingleList acc a),
      presentedIntervals.diffSingleList, cons, Set.sdiff_sdiff]

theorem diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) :
    presentedIntervals (_root_.DomainTheory.NeighbourhoodSystems.diffAllList p L2) =
      Set.Ico p.1 p.2 \ presentedIntervals L2 := by
  unfold _root_.DomainTheory.NeighbourhoodSystems.diffAllList
  rw [foldl_diffSingleList, cons, nil, Set.union_empty]

theorem diffLists (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (_root_.DomainTheory.NeighbourhoodSystems.diffLists L1 L2) =
      presentedIntervals L1 \ presentedIntervals L2 := by
  induction L1 with
  | nil => simp [_root_.DomainTheory.NeighbourhoodSystems.diffLists]
  | cons a l ih =>
    rw [show _root_.DomainTheory.NeighbourhoodSystems.diffLists (a :: l) L2 =
        _root_.DomainTheory.NeighbourhoodSystems.diffAllList a L2 ++
          _root_.DomainTheory.NeighbourhoodSystems.diffLists l L2 from rfl,
      append, presentedIntervals.diffAllList, ih, cons, Set.union_sdiff_distrib]
theorem map_clip (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map clip) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
  ext x
  simp only [mem, List.mem_map, Set.mem_inter_iff, Set.mem_Ico, clip]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hx0, hx1⟩
    exact ⟨(q.1 ⊔ 0, q.2 ⊓ 1), ⟨q, hq, rfl⟩, sup_le hxq1 hx0, lt_inf_iff.mpr ⟨hxq2, hx1⟩⟩

theorem filter_lt (L : List (ℚ × ℚ)) :
    presentedIntervals (L.filter (fun p => decide (p.1 < p.2))) = presentedIntervals L := by
  ext x
  simp only [mem, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx1, hx2⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hx1 hx2⟩, hx1, hx2⟩
theorem map_clipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (clipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, clipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

theorem map_clipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (clipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [mem, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, clipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

end presentedIntervals

end DomainTheory.NeighbourhoodSystems
