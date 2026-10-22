/-ai
The lower-bound information system on the natural numbers has bottom token zero, takes every finite set to be consistent, and uses the lower-bound entailment of Factoid 2.4, under which a set entails a number when the number is zero or is at most some member of the set. Subsets, singletons, and sets enlarged by an entailed token are consistent because every finite set is. Zero is entailed by the zero clause. A member of a consistent set is entailed by reflexivity of the numerical order. In a composite entailment, a conclusion equal to zero remains zero, and a conclusion bounded by an intermediate token is either zero, when that token is zero, or bounded by a token of the original set, by transitivity of the numerical order.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.InformationSystems.Factoid24
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.ScottMapBridge
public import DomainTheory.BridgeTheorems.SexDomainEquation

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

/-- Scott’s ℕ lower-bound information system (Factoid 2.4), as a named definition. -/
def lowerBoundSystem : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := Factoid24.lowerBoundEnt
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
