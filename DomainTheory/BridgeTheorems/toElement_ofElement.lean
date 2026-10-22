module

public import DomainTheory.BridgeTheorems.toElement
public import DomainTheory.BridgeTheorems.ofElement
public import DomainTheory.BridgeTheorems.ofElement_mem
public import DomainTheory.BridgeTheorems.interOf_singleton
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.toInfoSys
public import DomainTheory.BridgeTheorems.toElement_carrier

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem toElement_ofElement (e : B.toInfoSys.Element) :
    B.toElement (B.ofElement e) = e := by
  have hc : (B.toElement (B.ofElement e)).carrier = e.carrier := by
    ext i
    constructor
    · intro hi
      rcases (B.ofElement_mem e (B.nbhd i)).mp hi with ⟨_, j, hj, hsub⟩
      have hEnt : B.toInfoSys.Ent {j} i := by
        refine ⟨by simpa [B.interOf_singleton] using B.nbhd_mem j, ?_⟩
        simpa [B.interOf_singleton] using hsub
      exact e.closed {j} i (by
        intro x hx
        have : x = j := Finset.mem_singleton.mp hx
        exact this ▸ hj) hEnt
    · intro hi
      exact ⟨B.nbhd_mem i, i, hi, subset_rfl⟩
  rcases e with ⟨c, cons, clo⟩
  rcases hte : B.toElement (B.ofElement ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by
    simpa [hte, toElement_carrier] using hc
  subst hc'
  rfl

end NbhdBasis

end DomainTheory.BridgeTheorems
