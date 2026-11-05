module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Countable intersection of ideal elements: a neighbourhood belongs to the meet
iff it belongs to every term of the sequence. -/
def iInter (x : ℕ → V.Element) : V.Element where
  mem X := ∀ n, (x n).mem X
  sub h := (x 0).sub (h 0)
  master_mem n := (x n).master_mem
  inter_mem h1 h2 n := (x n).inter_mem (h1 n) (h2 n)
  up_mem h hY hXY n := (x n).up_mem (h n) hY hXY

@[simp] theorem mem_iInter (x : ℕ → V.Element) {X : Set α} :
    (V.iInter x).mem X ↔ ∀ n, (x n).mem X := Iff.rfl

theorem iInter_le (x : ℕ → V.Element) (n : ℕ) : V.iInter x ≤ x n :=
  fun _ h => h n

theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
