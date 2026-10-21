/-ai
The union of two universal neighbourhoods belongs to the universal system.

Each code presents a nonempty set of intervals contained in the master. The concatenation of the two decoded canonical lists presents the union. Nonemptiness of the first neighbourhood remains inside the union, and both neighbourhoods sit inside the master, so their union does.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem U_mem_union_UX (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨-, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨-, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨decodeQPairList (canonCode n) ++ decodeQPairList (canonCode m),
      (presentedIntervals_append _ _).symm⟩, hne1.mono Set.subset_union_left,
    Set.union_subset hsub1 hsub2⟩

end DomainTheory.NeighbourhoodSystems
