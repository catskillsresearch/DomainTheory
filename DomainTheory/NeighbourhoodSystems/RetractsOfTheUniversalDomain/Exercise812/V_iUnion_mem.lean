module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_union_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

















/-- **`V` is closed under finite (`Fintype`-indexed) unions**, as long as the result is
non-empty — mirrors `Definition87.lean`'s `U_iUnion_mem` verbatim. -/
theorem V_iUnion_mem {ι : Type*} [Fintype ι] {f : ι → Set ℕ} (hf : ∀ i, f i = ∅ ∨ V.mem (f i))
    (hne : (⋃ i, f i).Nonempty) : V.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ V.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact V_union_mem (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall] at hne ⊢
  exact (hstep Finset.univ).resolve_left hne.ne_empty

end DomainTheory.NeighbourhoodSystems
