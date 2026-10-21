/-ai
One step of the positive meet-fold takes an accumulator coding a success bit and an index, together with a next index. If the accumulator is successful and the consistency function accepts the pair of the current index with the next index, the step returns success paired with their intersection index; otherwise it returns failure paired with the current index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.IPos_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (cons : ℕ → ℕ)

/-- One step of the positive meet-fold. The accumulator `r` codes `(ok, idx)`
(`r.unpair.1 = ok`, `r.unpair.2 = idx`); `i` is the next positive-constraint index. If the fold is
still "ok" and `P`'s consistency decider accepts `(idx, i)`, advance to `P.inter idx i`; otherwise
the fold is permanently "not ok" (accumulator frozen at the last good `idx`, which is discarded by
`meetFold_spec` in that case anyway). -/
def meetStep (r i : ℕ) : ℕ :=
  selectFn (isOne r.unpair.1 * isOne (cons (Nat.pair r.unpair.2 i)))
    (Nat.pair 1 (P.inter r.unpair.2 i)) (Nat.pair 0 r.unpair.2)

end DomainTheory.NeighbourhoodSystems
