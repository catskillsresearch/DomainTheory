module

public import DomainTheory.BridgeTheorems.ConjScottMap
public import DomainTheory.BridgeTheorems.conjScottMapFun

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']

variable (ιD : D ≃o D') (ιE : E ≃o E')

noncomputable instance : CoeFun (ConjScottMap ιD ιE) (fun _ => D' → E') where
  coe g := conjScottMapFun ιD ιE g.scott

end ConjScottMap

end DomainTheory.BridgeTheorems
