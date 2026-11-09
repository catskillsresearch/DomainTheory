module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open treeSystem
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem sexAtom_mem_self (n : ℕ) : TreeToken.atom n ∈ (sexAtom n).carrier :=
  closure.subset SexSys (SexSys.con_sing _) (Finset.mem_singleton_self _)

end DomainTheory.BridgeTheorems
