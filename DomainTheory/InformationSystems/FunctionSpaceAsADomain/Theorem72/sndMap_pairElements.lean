/-ai
The second projection of the paired element of two elements is the second element.

Both inclusions are checked. A token in the projection comes from a product set inside the pair, and the second component of that set lies in the second element, so closure applies. Conversely, the right lift of the singleton of a token of the second element lies in the pair, because each such token records, by Factoid 3.2, the bottom token in the first element and that token in the second element. The second component of the right lift is the singleton, which entails itself by Proposition 2.3(iii).
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap






















theorem sndMap_pairElements (x : A.Element) (y : B.Element) :
    (sndMap A B).toElement (pairElements A B x y) = y := by
  apply le_antisymm
  · intro b ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(sndFinset A B s) ⊆ y.carrier := by
      intro c hc
      rcases (mem_sndFinset A B).1 hc with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).2 hbot
    exact y.closed _ b hsub (hEnt b (Finset.mem_singleton_self _))
  · intro b hb
    refine ⟨liftRight A B {b}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨c, hc, rfl⟩
      have : c = b := Finset.mem_singleton.mp hc
      subst this
      exact ⟨fun _ => factoid_3_2 A x, fun _ => hb⟩
    · refine ⟨ProdCon_liftRight A B (B.con_sing b), B.con_sing b, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (B.con_sing b)

end InfoSys
end DomainTheory.InformationSystems
