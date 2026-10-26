module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxShift
public import DomainTheory.DataTypesAsLattices.Closures.boxTag
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.union_botElem
public import DomainTheory.DataTypesAsLattices.Closures.botElem_union
public import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.topElem_ne_botElem
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_more
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** Sum of closures:
`a ⊞ b = λu.([u]₀ ⊃ 0, 0) ∪ ([u]₁ ⊃ 1, 1) ⊒ [a'([u]₀), ⊥], [⊥, b'([u]₁)]`.
The test is the union of the two occupancy tags, so an inhabited left
component dispatches to the left branch, an inhabited right component to
the right branch, both to `⊤` (via the doubly strict (4.4)) and neither
to `⊥`. -/
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
      (squarePair (funOf (boxShift a) (squareFst u)) botElem)
      (squarePair botElem (funOf (boxShift b) (squareSnd u))))

namespace boxPlus

/- `def`+`namespace boxPlus` shadows bare `eq_5_*`. -/
private abbrev squarePair_eta := _root_.DomainTheory.DataTypesAsLattices.eq_5_8
private abbrev squareFst_of_pair := _root_.DomainTheory.DataTypesAsLattices.eq_5_9
private abbrev squareSnd_of_pair := _root_.DomainTheory.DataTypesAsLattices.eq_5_10

theorem test_isScottContinuous :
    IsScottContinuous (fun u => boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u)) :=
  theorem_1_3.tuple
    (fun y => union_left_isScottContinuous y)
    (fun x => union_const_left_isScottContinuous x)
    (theorem_1_3 (boxTag.isScottContinuous 0) squareFst.isScottContinuous)
    (theorem_1_3 (boxTag.isScottContinuous 1) squareSnd.isScottContinuous)

theorem map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  theorem_1_3.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    test_isScottContinuous
    (theorem_1_3 (f := fun x => squarePair x botElem)
      (g := fun u => funOf (boxShift a) (squareFst u))
      (squarePair.isScottContinuous_left botElem)
      (theorem_1_3 (funOf.isScottContinuous (boxShift a)) squareFst.isScottContinuous))
    (theorem_1_3 (f := fun y => squarePair botElem y)
      (g := fun u => funOf (boxShift b) (squareSnd u))
      (squarePair.isScottContinuous_right botElem)
      (theorem_1_3 (funOf.isScottContinuous (boxShift b)) squareSnd.isScottContinuous))

theorem app (a b u : Pomega) :
    funOf (boxPlus a b) u =
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u))) :=
  beta (map_isScottContinuous a b) u

theorem app_empty {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u = botElem := by
  rw [app, hx, hy, boxTag.bot, boxTag.bot, Set.union_self, dcondSet.bot]

theorem app_left {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u =
      squarePair (funOf (boxShift a) (squareFst u)) botElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  rw [app, boxTag.of_mem hm, hy, boxTag.bot, union_botElem,
    dcondSet.ofNat_zero]

theorem app_right {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u =
      squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hy
  rw [app, boxTag.of_mem hm, hx, boxTag.bot, botElem_union,
    dcondSet.ofNat_one]

theorem app_mixed {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u = topElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  obtain ⟨k, hk⟩ := exists_mem_of_ne_bot hy
  rw [app, boxTag.of_mem hm, boxTag.of_mem hk]
  exact dcondSet.of_mixed (by simp [ofNat]) ⟨0, by simp [ofNat]⟩

theorem app_bot (a b : Pomega) :
    funOf (boxPlus a b) botElem = botElem :=
  app_empty squareFst.bot squareSnd.bot

theorem app_top (a b : Pomega) :
    funOf (boxPlus a b) topElem = topElem :=
  app_mixed (by rw [squareFst.top]; exact topElem_ne_botElem)
    (by rw [squareSnd.top]; exact topElem_ne_botElem)

theorem app_app {a b : Pomega} (ha : Retract a) (hb : Retract b)
    (u : Pomega) :
    funOf (boxPlus a b) (funOf (boxPlus a b) u) = funOf (boxPlus a b) u := by
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [app_empty hx hy, app_bot]
  · rw [app_right hx hy,
      app_right (u := squarePair botElem (funOf (boxShift b) (squareSnd u)))
        (squareFst_of_pair _ _) (by rw [squareSnd_of_pair]; exact boxShift.app_ne_bot b _),
      squareSnd_of_pair, retract_app (boxShift.isRetract hb)]
  · rw [app_left hx hy,
      app_left (u := squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (by rw [squareFst_of_pair]; exact boxShift.app_ne_bot a _) (squareSnd_of_pair _ _),
      squareFst_of_pair, retract_app (boxShift.isRetract ha)]
  · rw [app_mixed hx hy, app_top]

theorem isRetract {a b : Pomega} (ha : Retract a) (hb : Retract b) :
    Retract (boxPlus a b) := by
  constructor
  change boxPlus a b =
    graph (fun u => funOf (boxPlus a b) (funOf (boxPlus a b) u))
  apply graph_ext
  intro u
  rw [app_app ha hb u, app]

theorem expansive {a b : Pomega} (ha : Closure a) (hb : Closure b)
    (u : Pomega) : u ⊆ funOf (boxPlus a b) u := by
  have h8 : squarePair (squareFst u) (squareSnd u) = u := squarePair_eta u
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [hx, hy, squarePair.bot_bot] at h8
    rw [app_empty hx hy, ← h8]
  · rw [app_right hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
      rw [hx]
      exact squarePair.mono subset_rfl (boxShift.expansive hb (squareSnd u))
    rwa [h8] at hsub
  · rw [app_left hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair (funOf (boxShift a) (squareFst u)) botElem := by
      rw [hy]
      exact squarePair.mono (boxShift.expansive ha (squareFst u)) subset_rfl
    rwa [h8] at hsub
  · rw [app_mixed hx hy]
    exact fun k _ => Set.mem_univ k

theorem typed_bot (a b : Pomega) :
    typed botElem (boxPlus a b) :=
  (app_bot a b).symm

theorem typed_top (a b : Pomega) :
    typed topElem (boxPlus a b) :=
  (app_top a b).symm

theorem typed_inl {a b x : Pomega} (hx : typed x (boxShift a)) :
    typed (squarePair x botElem) (boxPlus a b) := by
  have hx0 : x ≠ botElem := by
    rw [hx]; exact boxShift.app_ne_bot a x
  rw [typed, app_left (by rw [squareFst_of_pair]; exact hx0) (squareSnd_of_pair _ _), squareFst_of_pair,
    ← hx]

theorem typed_inr {a b y : Pomega} (hy : typed y (boxShift b)) :
    typed (squarePair botElem y) (boxPlus a b) := by
  have hy0 : y ≠ botElem := by
    rw [hy]; exact boxShift.app_ne_bot b y
  rw [typed, app_right (squareFst_of_pair _ _) (by rw [squareSnd_of_pair]; exact hy0), squareSnd_of_pair,
    ← hy]

theorem typed_iff {a b u : Pomega} (ha : Retract a) (hb : Retract b) :
    typed u (boxPlus a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = squarePair x botElem ∧ typed x (boxShift a)) ∨
          (∃ y, u = squarePair botElem y ∧ typed y (boxShift b)) := by
  constructor
  · intro hu
    have hu' : u = funOf (boxPlus a b) u := hu
    by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
    · exact Or.inl (hu'.trans (app_empty hx hy))
    · refine Or.inr (Or.inr (Or.inr ⟨funOf (boxShift b) (squareSnd u), ?_, ?_⟩))
      · exact hu'.trans (app_right hx hy)
      · exact (retract_app (boxShift.isRetract hb) (squareSnd u)).symm
    · refine Or.inr (Or.inr (Or.inl ⟨funOf (boxShift a) (squareFst u), ?_, ?_⟩))
      · exact hu'.trans (app_left hx hy)
      · exact (retract_app (boxShift.isRetract ha) (squareFst u)).symm
    · exact Or.inr (Or.inl (hu'.trans (app_mixed hx hy)))
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact typed_bot a b
    · rw [hu]; exact typed_top a b
    · rw [hx]; exact typed_inl hxt
    · rw [hy]; exact typed_inr hyt


end boxPlus

end DomainTheory.DataTypesAsLattices
