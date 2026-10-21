/-ai
Under the characteristic and consistency hypotheses, the qChar-gated fold of every list, started at the master index, is diagonally fixed.

Apply the fold invariant to the master index, which is diagonally fixed.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.diagFixed_masterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_diagFixed_of_diagFixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)


variable {P qChar cons}

/-- **Correctness of the `qChar`-gated fold, instantiated at the real starting point
`P.masterIdx`.** -/
theorem myFold_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    DiagFixed P a (myFold P qChar cons l) :=
  myFold_diagFixed_of_diagFixed hqChar hcons l (diagFixed_masterIdx a)

end DomainTheory.NeighbourhoodSystems
