
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_subset_pre_fixed

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

namespace ApproximableMap

theorem fixElement_le_of_pre_fixed (f : ApproximableMap A A) (x : A.Element)
    (hpre : f.toElement x ≤ x) : fixElement A f ≤ x := by
  intro a ⟨w, hw, ⟨hwCon, haCon, v0, hv0, hEnt⟩⟩
  obtain ⟨n, hn⟩ := hv0
  have hsub := fixChain_subset_pre_fixed A f x hpre hw hn
  have hEnta : A.Ent v0 a := hEnt a (Finset.mem_singleton_self _)
  exact x.closed v0 a hsub hEnta

end ApproximableMap
end InfoSys

end DomainTheory.InformationSystems
