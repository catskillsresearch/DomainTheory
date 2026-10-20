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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_of_diagFixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)


variable {P qChar cons}

/-- **Theorem 8.8(c), Part 3 of 6, second half.** Every `fixedNbhd a`-neighbourhood `Y` is
`D_X qChar cons c` for some list-code `c`: `P.surj` finds `Y`'s raw `V`-index, which is `DiagFixed`
since `Y` is `a`-fixed, and `D_X_of_diagFixed` finishes it. -/
theorem D_X_surj {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {Y : Set α} (hY : (fixedNbhd a).mem Y) : ∃ c, D_X P qChar cons c = Y := by
  obtain ⟨hYV, hYa⟩ := hY
  obtain ⟨n₀, hn₀⟩ := P.surj hYV
  have hdiag : DiagFixed P a n₀ := by unfold DiagFixed; rw [hn₀]; exact hYa
  obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hdiag
  exact ⟨c, by rw [hc, hn₀]⟩

end DomainTheory.NeighbourhoodSystems
