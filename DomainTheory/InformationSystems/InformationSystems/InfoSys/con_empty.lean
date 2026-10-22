module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

universe u


namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)


/-- Empty set is consistent (subset of any singleton). -/
theorem con_empty : (∅ : Finset α) ∈ sys.Con :=
  sys.con_subset (sys.con_sing sys.bot) (Finset.empty_subset _)

end InfoSys
end DomainTheory.InformationSystems
