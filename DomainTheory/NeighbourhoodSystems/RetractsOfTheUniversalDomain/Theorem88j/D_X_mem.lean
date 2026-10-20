module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.diagFixed_masterIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStep_diagFixed_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_diagFixed_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFoldCode_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.primrec_myStepCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.primrec_myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.diagFixed_myFoldCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)


variable {P qChar cons}

/-- **Theorem 8.8(c), Part 3 of 6, first half.** Every `D_X qChar cons c` is a `fixedNbhd
a`-neighbourhood — Part 2's invariant `diagFixed_myFoldCode`, repackaged via
`diagFixed_iff_fixedNbhd_mem`. -/
theorem D_X_mem {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    (fixedNbhd a).mem (D_X P qChar cons c) :=
  (diagFixed_iff_fixedNbhd_mem P a _).mp (diagFixed_myFoldCode P qChar cons hqChar hcons c)

end DomainTheory.NeighbourhoodSystems
