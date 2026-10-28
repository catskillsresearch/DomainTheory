module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_4

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def principal {X : Set α} (hX : V.mem X) : V.Element where
  mem Y := V.mem Y ∧ X ⊆ Y
  sub h := h.1
  master_mem := ⟨V.master_mem, V.sub_master hX⟩
  inter_mem h1 h2 :=
    ⟨V.inter_mem h1.1 h2.1 hX (Set.subset_inter h1.2 h2.2), Set.subset_inter h1.2 h2.2⟩
  up_mem h hY hsub := ⟨hY, h.2.trans hsub⟩

@[simp] theorem mem_principal {X Y : Set α} (hX : V.mem X) :
    (V.principal hX).mem Y ↔ V.mem Y ∧ X ⊆ Y := Iff.rfl
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
