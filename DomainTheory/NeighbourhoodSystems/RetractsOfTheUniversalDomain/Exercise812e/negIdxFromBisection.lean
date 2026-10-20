module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

/-- **The split's "negative" (`\`-branch) index.** Same outer shape as `posIdxFromBisection`,
falling back to the bisection's *right* half instead of its left. -/
noncomputable def negIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.right m))

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
