/-ai
If a finite set lies in an element y, then its right lift lies in the paired element of any element x with y.

A token of the right lift is the right token of a member of the set, hence of y. The second-projection law places that member in the second projection of the pair, so it comes from a product set inside the pair that entails its singleton. Closure of the paired element under that entailment, with the first component sent to the bottom token, yields the right token.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndMap_pairElements

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






















theorem subset_pairElements_liftRight {x : A.Element} {y : B.Element}
    {v : Finset β} (hv : ↑v ⊆ y.carrier) :
    ↑(liftRight A B v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
  have hby : b ∈ y.carrier := hv (Finset.mem_coe.2 hb)
  have : b ∈ ((sndMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [sndMap_pairElements] using hby
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkRight A B b) hs ⟨hCon,
    fun _ => A.ent_bot hCon.1,
    fun _ => hEnt b (Finset.mem_singleton_self _)⟩

end InfoSys
end DomainTheory.InformationSystems
