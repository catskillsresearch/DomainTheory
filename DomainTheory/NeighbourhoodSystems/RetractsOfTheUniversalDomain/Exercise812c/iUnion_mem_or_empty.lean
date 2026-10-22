module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.hcoreIdxYc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88e.transfer_dir_idxYc
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **`Fintype`-indexed union-closure from `IsPositive` + `DiffClosed` alone**, generalizing
`Definition87.lean`'s `U_iUnion_mem`/`Exercise812.lean`'s `V_iUnion_mem` to an abstract `D`. Proved
identically (fold `union_mem_or_empty` over `Finset.univ`), just with the generic one-step lemma in
place of `U`/`V`'s hardcoded binary-union facts. -/
theorem iUnion_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {ι : Type*} [Fintype ι] {f : ι → Set γ}
    (hf : ∀ i, f i = ∅ ∨ D.mem (f i)) : (⋃ i, f i) = ∅ ∨ D.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ D.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact union_mem_or_empty hpos hdiff (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall]
  exact hstep Finset.univ

end DomainTheory.NeighbourhoodSystems
