module

public import DomainTheory.InformationSystems.InformationSystems.a_first_example
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.BridgeTheorems.ScottMapBridge
public import DomainTheory.BridgeTheorems.SexDomainEquation

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

def lowerBoundSystem : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := lowerBoundEnt
  con_subset := by
    intro u v _ _
    exact Set.mem_univ v
  con_sing := by
    intro _
    exact Set.mem_univ _
  ent_con := by
    intro u a _
    exact Set.mem_univ _
  ent_bot := by
    intro u _
    exact Or.inl rfl
  ent_refl := by
    intro u a _ ha
    exact Or.inr ⟨a, ha, le_rfl⟩
  ent_trans := by
    intro u v c _ _ hvEnt huEnt
    rcases huEnt with rfl | ⟨n, hn, hcn⟩
    · exact Or.inl rfl
    · rcases hvEnt n hn with rfl | ⟨k, hk, hnk⟩
      · exact Or.inl (Nat.le_zero.mp hcn)
      · exact Or.inr ⟨k, hk, le_trans hcn hnk⟩

end DomainTheory.BridgeTheorems
