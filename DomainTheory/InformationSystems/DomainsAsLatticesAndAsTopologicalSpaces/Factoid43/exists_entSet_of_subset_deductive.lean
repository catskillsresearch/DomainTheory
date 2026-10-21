/-ai
If a finite set is contained in the deductive closure of a finitely consistent set, then some finite subset of that set entails every member of the finite set.

The proof is by induction on the finite set. The empty set is entailed by the empty set. For an insertion of a token into a finite set, one finite subset entails the inserted token and, by the inductive hypothesis, another entails every member of the remaining set. Their union is contained in the original set, hence consistent. Transitivity of entailment along the reflexive entailment of each summand from the union yields the required entailment.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.IsFinitelyConsistent

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Witness: some finite `w ⊆ U` entails every member of `Y ⊆ deductiveClosure U`. -/
theorem exists_entSet_of_subset_deductive
    (U : Set α) (hU : sys.IsFinitelyConsistent U) (Y : Finset α)
    (hY : (Y : Set α) ⊆ {a | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a}) :
    ∃ w : Finset α, (w : Set α) ⊆ U ∧ sys.EntSet w Y := by
  induction Y using Finset.induction_on with
  | empty =>
    exact ⟨∅, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha)),
      fun _ ha => False.elim (Finset.notMem_empty _ ha)⟩
  | insert a s _ha ih =>
    have ha' : ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u a :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ {b | ∃ u : Finset α, (u : Set α) ⊆ U ∧ sys.Ent u b} := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨ua, hua, hEnta⟩ := ha'
    obtain ⟨us, hus, hEnts⟩ := ih hs'
    refine ⟨ua ∪' us, ?_, ?_⟩
    · intro z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · intro b hb
      have hwU : (ua ∪' us : Set α) ⊆ U := by
        intro z hz
        rcases mem_funion.mp (Finset.mem_coe.1 hz) with h | h
        · exact hua (Finset.mem_coe.2 h)
        · exact hus (Finset.mem_coe.2 h)
      have hw : ua ∪' us ∈ sys.Con := hU _ hwU
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact sys.ent_trans hw (hU ua hua)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inl hy))) hEnta
      · exact sys.ent_trans hw (hU us hus)
          (fun y hy => sys.ent_refl hw (mem_funion.mpr (Or.inr hy))) (hEnts b hb')

end InfoSys

end DomainTheory.InformationSystems
