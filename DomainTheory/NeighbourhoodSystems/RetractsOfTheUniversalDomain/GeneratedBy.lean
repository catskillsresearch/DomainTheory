module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Combinatorics.Colex

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

inductive GeneratedBy {α : Type*} (g : ℕ → Set α) : Set α → Prop
  | of (i : ℕ) : GeneratedBy g (g i)
  | univ : GeneratedBy g Set.univ
  | inter {X Y} : GeneratedBy g X → GeneratedBy g Y → GeneratedBy g (X ∩ Y)
  | union {X Y} : GeneratedBy g X → GeneratedBy g Y → GeneratedBy g (X ∪ Y)
  | compl {X} : GeneratedBy g X → GeneratedBy g Xᶜ

def bitmaskOf (s : Finset ℕ) : ℕ := ∑ j ∈ s, 2 ^ j

theorem testBit_sum_two_pow {s : Finset ℕ} {i : ℕ} : (∑ j ∈ s, 2 ^ j).testBit i ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

@[simp] theorem testBit_bitmaskOf {s : Finset ℕ} {i : ℕ} : (bitmaskOf s).testBit i ↔ i ∈ s :=
  testBit_sum_two_pow

def generator (i : ℕ) : Set ℕ := {n : ℕ | n.testBit i = true}

@[simp] theorem mem_generator {i n : ℕ} : n ∈ generator i ↔ n.testBit i = true := Iff.rfl

end DomainTheory.NeighbourhoodSystems
end
