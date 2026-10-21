/-ai
If a neighbourhood is contained in the folded intersection of a finite set of basis neighbourhoods, then that folded intersection is itself a neighbourhood.

The proof is by induction on the finite set. The empty intersection is the master set. At an insertion of a fresh index, the intersection is the neighbourhood of that index cut with the intersection of the remaining set. The inductive hypothesis, applied to the containment in the second factor, makes the remaining intersection a neighbourhood, and the system closes under cutting the neighbourhood of the new index with that set, using the given neighbourhood as the lower bound.
ai-/
module

public import Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_empty
public import DomainTheory.BridgeTheorems.interOf_insert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- If a neighbourhood sits below `interOf u`, then `interOf u ∈ 𝒟`. -/
theorem interOf_mem_of_lower_bound {u : Finset ι} {Z : Set α}
    (hZ : B.system.mem Z) (hsub : Z ⊆ B.interOf u) : B.system.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using B.system.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha] at hsub ⊢
    have hs : B.system.mem (B.interOf s) := ih (hsub.trans Set.inter_subset_right)
    exact B.system.inter_mem (B.nbhd_mem a) hs hZ hsub

end NbhdBasis

end DomainTheory.BridgeTheorems
