module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_iff_fixedNbhd_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_isREPred
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.diagFixed_exists_qChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88i.myFold_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

variable (P qChar cons)

/-- `foldCode`-shaped step matching `myStep`: state `w = pair e (pair r params)` (`params`
unused). -/
def myStepCode (w : ℕ) : ℕ := myStep P qChar cons w.unpair.2.unpair.1 w.unpair.1

end DomainTheory.NeighbourhoodSystems
