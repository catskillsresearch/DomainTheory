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

/-- Directed supremum of a nonempty directed family of ideal elements: a neighbourhood
belongs to the join iff it belongs to some member of the family. -/
def sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) : V.Element where
  mem Z := ∃ s ∈ S, s.mem Z
  sub := fun ⟨s, _, hs⟩ => s.sub hs
  master_mem := by obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, s.master_mem⟩
  inter_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ ⟨b, hbS, hbZ⟩
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a haS b hbS
    exact ⟨c, hcS, c.inter_mem (hac Z haZ) (hbc Z' hbZ)⟩
  up_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ hZ' hZZ'
    exact ⟨a, haS, a.up_mem haZ hZ' hZZ'⟩

theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

theorem sSupDirected_le (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {y : V.Element}
    (hy : ∀ s ∈ S, s ≤ y) : V.sSupDirected S hne hdir ≤ y := by
  rintro Z ⟨s, hs, hsZ⟩
  exact hy s hs Z hsZ

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
