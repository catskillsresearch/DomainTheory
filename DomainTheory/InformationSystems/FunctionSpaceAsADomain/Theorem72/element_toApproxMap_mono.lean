/-ai
The relation recovered from a function-space element is monotone for entailment: a related pair may be replaced by an entailing input and an entailed output, provided the new sets are consistent.

The singleton of the original token lies in the element. It entails the new token, by the given input entailment and, after the output union of a singleton, the given output entailment. Closure of the element puts the new token in the carrier.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- The recovered relation is monotone for entailment. -/
theorem element_toApproxMap_mono (x : (functionSystem A B).Element) :
    ∀ {u u' : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con →
      ∃ (hu : u' ∈ A.Con) (hv : v' ∈ B.Con),
        mkFunToken A B u' v' hu hv ∈ x.carrier := by
  rintro u u' v v' ⟨hu, hv, hp⟩ hEntu hEntv hu' hv'
  refine ⟨hu', hv', ?_⟩
  let p := mkFunToken A B u v hu hv
  let r := mkFunToken A B u' v' hu' hv'
  have hwsub : (↑({p} : Finset (FunToken A B)) : Set _) ⊆ x.carrier := by
    intro t ht
    have : t = p := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
    subst this
    exact hp
  have hEnt : FunEnt A B {p} r := by
    refine ⟨x.consistent {p} hwsub, {p}, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hEntu
    · rw [funOutputUnion_singleton]
      exact hEntv
  exact x.closed {p} r hwsub hEnt

end InfoSys

end DomainTheory.InformationSystems
