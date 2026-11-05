module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Attr.Core

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Directed (monotone) countable union of ideal elements: a neighbourhood belongs to the
join iff it belongs to some term of the sequence. -/
def iUnion (x : ℕ → V.Element) (hmono : Monotone x) : V.Element where
  mem X := ∃ n, (x n).mem X
  sub := by rintro X ⟨n, hn⟩; exact (x n).sub hn
  master_mem := ⟨0, (x 0).master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, (x (max n m)).inter_mem ?_ ?_⟩
    · exact hmono (le_max_left n m) X hn
    · exact hmono (le_max_right n m) Y hm
  up_mem := by
    rintro X Y ⟨n, hn⟩ hY hXY
    exact ⟨n, (x n).up_mem hn hY hXY⟩

@[simp] theorem mem_iUnion (x : ℕ → V.Element) (hmono : Monotone x) {X : Set α} :
    (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X := Iff.rfl

theorem le_iUnion (x : ℕ → V.Element) (hmono : Monotone x) (n : ℕ) :
    x n ≤ V.iUnion x hmono :=
  fun _ hX => ⟨n, hX⟩

theorem iUnion_le (x : ℕ → V.Element) (hmono : Monotone x) (y : V.Element)
    (h : ∀ n, x n ≤ y) : V.iUnion x hmono ≤ y := by
  rintro X ⟨n, hn⟩
  exact h n X hn

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
