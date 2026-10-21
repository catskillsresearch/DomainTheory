/-ai
If a function-space element contains the tokens for one input and two outputs, then it contains the token for that input and the choice-free union of the two outputs.

The two tokens form a consistent set in the element. Their input union is the input united with itself, hence the input, so function consistency yields consistency of the output union after commutativity. The same two-token set entails the combined token: each input is entailed by reflexivity and Proposition 2.3(iii), and the output union of the set commutes to the combined output, which is entailed by reflexivity. Closure of the element supplies the token.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_self
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_comm_β

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Output-union of two related pairs remains related. -/
theorem element_toApproxMap_union_right (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      (∃ (hu : u ∈ A.Con) (hv : v' ∈ B.Con), mkFunToken A B u v' hu hv ∈ x.carrier) →
      ∃ (hu : u ∈ A.Con) (hv : v ∪' v' ∈ B.Con),
        mkFunToken A B u (v ∪' v') hu hv ∈ x.carrier := by
  rintro u v v' ⟨hu, hv, hp⟩ ⟨hu', hv', hq⟩
  have hvU : v ∪' v' ∈ B.Con := by
    have hCon : FunCon A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) := by
      apply x.consistent
      intro r hr
      rcases Finset.mem_insert.mp (Finset.mem_coe.1 hr) with rfl | hr
      · exact hq
      · have : r = mkFunToken A B u v hu hv := Finset.mem_singleton.mp hr
        subst this
        exact hp
    have hin : funInputUnion A B
        (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) ∈ A.Con := by
      rw [funInputUnion_insert, funInputUnion_singleton]
      change u ∪' u ∈ A.Con
      rw [funion_self]
      exact hu
    have hout := hCon _ (Finset.Subset.refl _) hin
    rw [funOutputUnion_insert, funOutputUnion_singleton, funion_comm_β] at hout
    exact hout
  refine ⟨hu, hvU, ?_⟩
  let p := mkFunToken A B u v hu hv
  let q := mkFunToken A B u v' hu' hv'
  let r := mkFunToken A B u (v ∪' v') hu hvU
  let w : Finset (FunToken A B) := insert q {p}
  have hwsub : (↑w : Set _) ⊆ x.carrier := by
    intro t ht
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 ht) with rfl | ht
    · exact hq
    · have : t = p := Finset.mem_singleton.mp ht
      subst this
      exact hp
  have hEnt : FunEnt A B w r := by
    refine ⟨x.consistent w hwsub, w, Finset.Subset.refl _, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact proposition_2_3_iii A hu'
      · have : t = p := Finset.mem_singleton.mp ht
        subst this
        exact proposition_2_3_iii A hu
    · have houtEq : funOutputUnion A B w = v' ∪' v := by
        change funOutputUnion A B
          (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) = v' ∪' v
        rw [funOutputUnion_insert, funOutputUnion_singleton]
        simp only [mkFunToken]
      rw [houtEq, funion_comm_β]
      exact proposition_2_3_iii B hvU
  exact x.closed w r hwsub hEnt

end InfoSys

end DomainTheory.InformationSystems
