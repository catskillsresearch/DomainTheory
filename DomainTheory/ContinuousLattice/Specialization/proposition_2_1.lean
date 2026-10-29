module

public import DomainTheory.ContinuousLattice.Specialization.MonotoneNet
public import DomainTheory.ContinuousLattice.Specialization.ScottConvergesTo

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

variable {D : Type u} [CompleteLattice D]

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

variable {x : ι → D} {L y : D}

namespace proposition_2_1

omit [IsDirected ι (· ≤ ·)] in
theorem le_of_converges (hL : IsLUB (range x) L) (hconv : ScottConvergesTo x y) : y ≤ L := by
  by_contra hyL
  obtain ⟨i, hi⟩ := hconv {z : D | ¬ z ≤ L} (ScottOpen.not_le L) hyL
  exact hi i le_rfl (hL.1 ⟨i, rfl⟩)

theorem of_le [Nonempty ι] (hx : MonotoneNet x) (hL : IsLUB (range x) L) (hyL : y ≤ L) :
    ScottConvergesTo x y := by
  intro U hU hyU
  have hdir : DirectedOn (· ≤ ·) (range x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    exact ⟨x k, ⟨k, rfl⟩, hx.out hik, hx.out hjk⟩
  have hLU : sSup (range x) ∈ U := by
    rw [IsLUB.sSup_eq hL]
    exact hU.1 hyL hyU
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.range_nonempty x) hdir hLU
  obtain ⟨i₀, rfl⟩ := hsS
  refine ⟨i₀, fun j hj => hU.1 (hx.out hj) hsU⟩

end proposition_2_1

theorem proposition_2_1 [Nonempty ι] (hx : MonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L :=
  ⟨fun hconv => proposition_2_1.le_of_converges hL hconv, proposition_2_1.of_le hx hL⟩

end DomainTheory.ContinuousLattice
