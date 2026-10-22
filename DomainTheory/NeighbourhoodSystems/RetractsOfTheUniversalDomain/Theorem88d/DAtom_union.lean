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


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- **The `D`-side atom splits along any prepended index** (Scott's `Δ = idxSetₙ ∪ (Δ∖idxSetₙ)`,
pulled back through `DAtom`): needed to show that once the "negative refinement" of a nonempty atom
is empty, the atom already coincides with its own "positive refinement" outright. -/
theorem DAtom_union (i : ℕ) (pos neg : List ℕ) :
    DAtom (P0 P) pos neg = DAtom (P0 P) (i :: pos) neg ∪ DAtom (P0 P) pos (i :: neg) := by
  ext m
  simp only [mem_DAtom, Set.mem_union, List.mem_cons, forall_eq_or_imp]
  by_cases hm : (P0 P).X m ⊆ (P0 P).X i <;> tauto

end DomainTheory.NeighbourhoodSystems
