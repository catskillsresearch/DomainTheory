module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntN_of_mem

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















theorem LamEnt_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamCon A u) (ht : t ∈ u) : LamEnt A u t := by
  rcases hu with ⟨n, hu⟩
  exact ⟨n, LamEntN_of_mem A hu ht⟩

end InfoSys
end DomainTheory.InformationSystems
