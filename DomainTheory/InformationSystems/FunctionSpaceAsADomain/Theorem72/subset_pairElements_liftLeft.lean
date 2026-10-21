/-ai
If a finite set lies in an element x, then its left lift lies in the paired element of x with any element y.

A token of the left lift is the left token of a member of the set, hence of x. The first-projection law places that member in the first projection of the pair, so it comes from a product set inside the pair that entails its singleton. Closure of the paired element under that entailment, with the second component sent to the bottom token, yields the left token.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstMap_pairElements

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






















theorem subset_pairElements_liftLeft {x : A.Element} {y : B.Element}
    {u : Finset α} (hu : ↑u ⊆ x.carrier) :
    ↑(liftLeft A B u) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨a, ha, rfl⟩
  have hax : a ∈ x.carrier := hu (Finset.mem_coe.2 ha)
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [fstMap_pairElements] using hax
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkLeft A B a) hs ⟨hCon,
    fun _ => hEnt a (Finset.mem_singleton_self _),
    fun _ => B.ent_bot hCon.2⟩

end InfoSys
end DomainTheory.InformationSystems
