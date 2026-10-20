module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_exists

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`∪`, for `𝒰`**: trivially recursively decidable (the always-`1` constant), since
`U_union_exists` shows the underlying predicate is unconditionally `True`. -/
theorem U_union_computable : RecDecidable₂ (fun n m => ∃ k, UX k = UX n ∪ UX m) :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun t => iff_of_true (U_union_exists t.unpair.1 t.unpair.2) rfl⟩

end DomainTheory.NeighbourhoodSystems
