module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

/-- **The `.inter` field for `D_X`**: concatenate the two list-codes (`Recursive.lean`'s
Exercise 7.22 `appendListCode`), reusing that this is exactly `myFoldCode`'s left-fold-from-
`P.masterIdx` restarted at `myFoldCode c₁` (via `List.foldl_append`). -/
def D_inter (c₁ c₂ : ℕ) : ℕ := appendListCode c₁ c₂

end DomainTheory.NeighbourhoodSystems
