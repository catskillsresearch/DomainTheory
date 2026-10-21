/-ai
If a finite set of tokens is contained in the set of tokens that an approximable mapping relates to some finite subset of an element, then some finite set contained in that element is related to the whole finite set.

The proof is by induction on the finite set. The empty set is contained in the element, and monotonicity applied to the empty relation, with the empty entailments, relates it to the empty set. For an insertion of a token into a finite set, the hypothesis gives a finite subset related to the singleton of that token, and the inductive hypothesis gives a finite subset related to the remaining set. Their union is contained in the element, so it is consistent. Reflexivity of entailment puts each summand below the union, and monotonicity transports the two relations. Closure under union on the right, with the identity of a singleton union and insertion, gives the relation to the inserted set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.singleton_funion_eq

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- Given `↑Y ⊆ f(x).carrier`, produce `u ⊆ x` with `u f Y`. -/
theorem exists_rel_of_subset_image (f : ApproximableMap A B) (x : A.Element)
    (Y : Finset β)
    (hY : ↑Y ⊆ ({Y : β | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}} : Set β)) :
    ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u Y := by
  induction Y using Finset.induction_on with
  | empty =>
    refine ⟨∅, ?_, ?_⟩
    · intro a ha
      exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
    · exact f.mono f.empty_rel (A.entSet_empty ∅) (B.entSet_empty ∅) A.con_empty B.con_empty
  | insert a s _ha ih =>
    have ha' : ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {a} :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' :
        ↑s ⊆ ({Y : β | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}} : Set β) := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨ua, hua, hrela⟩ := ha'
    obtain ⟨us, hus, hrels⟩ := ih hs'
    refine ⟨ua ∪' us, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ua ∪' us := Finset.mem_coe.1 hz
      rcases mem_funion.mp hz' with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · have hUcon : ua ∪' us ∈ A.Con :=
        x.consistent (ua ∪' us) fun z hz => by
          rcases mem_funion.mp hz with h | h
          · exact hua (Finset.mem_coe.2 h)
          · exact hus (Finset.mem_coe.2 h)
      have hEnt_ua : A.EntSet (ua ∪' us) ua :=
        fun y hy => A.ent_refl hUcon (subset_funion_left ua us hy)
      have hEnt_us : A.EntSet (ua ∪' us) us :=
        fun y hy => A.ent_refl hUcon (subset_funion_right ua us hy)
      have h1 : f.rel (ua ∪' us) {a} :=
        f.mono hrela hEnt_ua
          (fun z hz => by
            rw [Finset.mem_singleton] at hz
            rw [hz]
            exact B.ent_refl (B.con_sing a) (Finset.mem_singleton_self a))
          hUcon (B.con_sing a)
      have h2 : f.rel (ua ∪' us) s :=
        f.mono hrels hEnt_us (proposition_2_3_iii B (f.rel_cod hrels))
          hUcon (f.rel_cod hrels)
      have hU : f.rel (ua ∪' us) ({a} ∪' s) := f.union_right h1 h2
      simpa [singleton_funion_eq] using hU

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
