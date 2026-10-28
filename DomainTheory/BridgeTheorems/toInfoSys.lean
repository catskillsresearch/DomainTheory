module

public import DomainTheory.BridgeTheorems.interOf
public import DomainTheory.BridgeTheorems.interOf_mem_of_lower_bound
public import DomainTheory.BridgeTheorems.interOf_anti
public import DomainTheory.BridgeTheorems.interOf_subset_master
public import DomainTheory.BridgeTheorems.interOf_subset_nbhd
public import DomainTheory.BridgeTheorems.mem_interOf
public import DomainTheory.BridgeTheorems.interOf_singleton
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.BridgeTheorems.NbhdBasis
public import DomainTheory.BridgeTheorems.interOf_empty

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

def toInfoSys : InfoSys ι where
  bot := B.botIdx
  Con := {u | B.system.mem (B.interOf u)}
  Ent := fun u a => B.system.mem (B.interOf u) ∧ B.interOf u ⊆ B.nbhd a
  con_subset := by
    intro u v hu hv
    exact B.interOf_mem_of_lower_bound hu (B.interOf_anti hv)
  con_sing := by
    intro a
    simpa [Set.mem_ofPred_eq, B.interOf_singleton] using B.nbhd_mem a
  ent_con := by
    intro u a ⟨hu, hsub⟩
    have h₁ : B.interOf (insert a u) ⊆ B.interOf u :=
      B.interOf_anti (Finset.subset_insert a u)
    have h₂ : B.interOf u ⊆ B.interOf (insert a u) := by
      intro x hx
      refine B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hsub hx
      · exact (B.mem_interOf.mp hx).2 i hi
    have heq : B.interOf (insert a u) = B.interOf u := Set.Subset.antisymm h₁ h₂
    simpa [Set.mem_ofPred_eq, heq] using hu
  ent_bot := by
    intro u hu
    refine ⟨hu, ?_⟩
    intro x hx
    rw [B.botIdx_eq]
    exact B.interOf_subset_master u hx
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, B.interOf_subset_nbhd ha⟩
  ent_trans := by
    intro u v c hv _hu hall ⟨_, hsub⟩
    refine ⟨hv, ?_⟩
    intro x hx
    have hxu : x ∈ B.interOf u :=
      B.mem_interOf.mpr ⟨B.interOf_subset_master v hx, fun i hi => (hall i hi).2 hx⟩
    exact hsub hxu

end NbhdBasis

end DomainTheory.BridgeTheorems
