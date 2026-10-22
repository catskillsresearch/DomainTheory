module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_two_pow_found

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- **The closed-form membership characterization of `YseqCode`** — the "Set-level closed form"
this part exists to supply: a point lies in `UX (YseqCode P n)` iff it lies in some genuine
(non-junk) depth-`(n+1)` atom with bit `n` forced `1`. -/
theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

end DomainTheory.NeighbourhoodSystems
