module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_split'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.SplitSpec'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem splitChoice'_isSplitSpec {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal) :
    SplitSpec' (α := α) E (splitChoice' E hEnomin) := by
  intro A B hAB hBE Xn
  classical
  unfold splitChoice'
  rw [dite_eq_left ⟨hAB, hBE⟩]
  exact (exists_split' hEnomin hAB hBE Xn).choose_spec.choose_spec

end DomainTheory.NeighbourhoodSystems
