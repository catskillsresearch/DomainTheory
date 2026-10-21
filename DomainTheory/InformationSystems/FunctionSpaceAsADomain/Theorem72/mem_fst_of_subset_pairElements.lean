/-ai
If a set of product tokens lies in the paired element of x and y, then every token of its first component lies in x.

Consistency of the paired element makes the set product-consistent. Reflexivity of entailment places the token in the first projection of the pair, and the first-projection law rewrites that projection as x.
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

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


/-- Tokens in `fstFinset s` for `s ⊆ ⟨x,y⟩` lie in `x`. -/
theorem mem_fst_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {a : α}
    (ha : a ∈ fstFinset A B s) : a ∈ x.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, A.con_sing a, ?_⟩⟩
    intro b hb
    have : b = a := Finset.mem_singleton.mp hb
    subst this
    exact A.ent_refl hCon.1 ha
  simpa [fstMap_pairElements] using this

end InfoSys
end DomainTheory.InformationSystems
