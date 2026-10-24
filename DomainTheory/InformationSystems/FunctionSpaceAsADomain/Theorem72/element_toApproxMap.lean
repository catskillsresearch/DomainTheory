module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_comm_β
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funion_self
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement

@[expose] public section

namespace DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- The empty pair is related. -/
theorem element_toApproxMap.empty_rel (x : (functionSystem A B).Element) :
    ∃ (hu : (∅ : Finset α) ∈ A.Con) (hv : (∅ : Finset β) ∈ B.Con),
      mkFunToken A B ∅ ∅ hu hv ∈ x.carrier := by
  refine ⟨A.con_empty, B.con_empty, ?_⟩
  change funBot A B ∈ x.carrier
  exact factoid_3_2 (functionSystem A B) x

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- The recovered relation is monotone for entailment. -/
theorem element_toApproxMap.mono (x : (functionSystem A B).Element) :
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
    · rw [funOutputUnion.singleton]
      exact hEntv
  exact x.closed {p} r hwsub hEnt

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Codomain of the relation recovered from a function-space element. -/
theorem element_toApproxMap.rel_cod (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      v ∈ B.Con :=
  fun ⟨_, hv, _⟩ => hv

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Domain of the relation recovered from a function-space element. -/
theorem element_toApproxMap.rel_dom (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      u ∈ A.Con :=
  fun ⟨hu, _, _⟩ => hu

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Output-union of two related pairs remains related. -/
theorem element_toApproxMap.union_right (x : (functionSystem A B).Element) :
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
      rw [funInputUnion.insert, funInputUnion.singleton]
      change u ∪' u ∈ A.Con
      rw [funion_self]
      exact hu
    have hout := hCon _ (Finset.Subset.refl _) hin
    rw [funOutputUnion.insert, funOutputUnion.singleton, funion_comm_β] at hout
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
        rw [funOutputUnion.insert, funOutputUnion.singleton]
        simp only [mkFunToken]
      rw [houtEq, funion_comm_β]
      exact proposition_2_3_iii B hvU
  exact x.closed w r hwsub hEnt

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap.rel_dom A B x
  rel_cod := element_toApproxMap.rel_cod A B x
  empty_rel := element_toApproxMap.empty_rel A B x
  union_right := element_toApproxMap.union_right A B x
  mono := element_toApproxMap.mono A B x

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


open ApproximableMap


theorem element_toApproxMap.approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (InfoSys.approxMap_toElement A B f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨hu, hv, hp⟩
    change f.rel u v at hp
    exact hp
  · intro hrel
    exact ⟨f.rel_dom hrel, f.rel_cod hrel, by
      change f.rel u v
      exact hrel⟩

end InfoSys
end

end DomainTheory.InformationSystems
