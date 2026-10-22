module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_union_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`U` is closed under finite (`Fintype`-indexed) unions**, as long as the result is
non-empty: if every `f i` is either empty or a `U`-neighbourhood, so is `⋃ i, f i` (given it is
non-empty). Proved by folding `U_union_mem` over `Finset.univ` (`Finset.induction_on`). -/
theorem U_iUnion_mem {ι : Type*} [Fintype ι] {f : ι → Set ℚ} (hf : ∀ i, f i = ∅ ∨ U.mem (f i))
    (hne : (⋃ i, f i).Nonempty) : U.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ U.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact U_union_mem (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall] at hne ⊢
  exact (hstep Finset.univ).resolve_left hne.ne_empty

end DomainTheory.NeighbourhoodSystems
