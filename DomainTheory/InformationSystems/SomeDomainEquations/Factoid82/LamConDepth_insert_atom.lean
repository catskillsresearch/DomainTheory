module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamAtomFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_of_fun_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Inserting an entailed atom preserves depth-Con. -/
theorem LamConDepth_insert_atom {u : Finset (RawLamToken α)} {x : α}
    (ht : LamEntDepth A u (.atom x)) :
    LamConDepth A (insert (.atom x) u) := by
  have : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  cases ht with
  | atom hu hF _hne hEnt =>
    have hF' : lamFunFinset (insert (.atom x) u) = ∅ := by
      rw [lamFunFinset_insert_atom]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_atom]
      exact A.ent_con hEnt)

end InfoSys

end DomainTheory.InformationSystems
