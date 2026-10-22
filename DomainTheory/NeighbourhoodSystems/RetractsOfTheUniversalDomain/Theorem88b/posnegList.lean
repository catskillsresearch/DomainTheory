module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.P0_X

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The `(pos, neg)` accumulator pair for a sign sequence `δ`, at depth `n`.** Mirrors
`genAtom`'s own recursion: at step `n`, `n` itself joins `pos` (if `δ n = true`) or `neg`
(otherwise). -/
def posnegList (δ : ℕ → Bool) : ℕ → List ℕ × List ℕ
  | 0 => ([], [])
  | n + 1 =>
      let pn := posnegList δ n
      if δ n then (pn.1 ++ [n], pn.2) else (pn.1, pn.2 ++ [n])

end DomainTheory.NeighbourhoodSystems
