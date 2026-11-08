module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

theorem ext {f g : ApproximableMap A B} (h : ∀ u v, f.rel u v ↔ g.rel u v) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by
    funext u v
    exact propext (h u v)
  subst this
  rfl

theorem singleton_funion_eq (a : β) (s : Finset β) :
    ({a} : Finset β) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases funion.mem.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact funion.mem.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact funion.mem.mpr (Or.inr hs)

theorem exists_rel_of_subset_image (f : ApproximableMap A B) (x : A.Element)
    (Y : Finset β)
    (hY : ↑Y ⊆ ({Y : β | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}} : Set β)) :
    ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u Y := by
  induction Y using Finset.induction_on with
  | empty =>
    refine ⟨∅, ?_, ?_⟩
    · intro a ha
      exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
    · exact f.mono f.empty_rel (EntSet.empty A ∅) (EntSet.empty B ∅) A.con_empty B.con_empty
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
      rcases funion.mem.mp hz' with h | h
      · exact hua (Finset.mem_coe.2 h)
      · exact hus (Finset.mem_coe.2 h)
    · have hUcon : ua ∪' us ∈ A.Con :=
        x.consistent (ua ∪' us) fun z hz => by
          rcases funion.mem.mp hz with h | h
          · exact hua (Finset.mem_coe.2 h)
          · exact hus (Finset.mem_coe.2 h)
      have hEnt_ua : A.EntSet (ua ∪' us) ua :=
        fun y hy => A.ent_refl hUcon (funion.subset_left ua us hy)
      have hEnt_us : A.EntSet (ua ∪' us) us :=
        fun y hy => A.ent_refl hUcon (funion.subset_right ua us hy)
      have h1 : f.rel (ua ∪' us) {a} :=
        f.mono hrela hEnt_ua
          (fun z hz => by
            rw [Finset.mem_singleton] at hz
            rw [hz]
            exact B.ent_refl (B.con_sing a) (Finset.mem_singleton_self a))
          hUcon (B.con_sing a)
      have h2 : f.rel (ua ∪' us) s :=
        f.mono hrels hEnt_us (proposition_2_3.iii B (f.rel_cod hrels))
          hUcon (f.rel_cod hrels)
      have hU : f.rel (ua ∪' us) ({a} ∪' s) := f.union_right h1 h2
      simpa [singleton_funion_eq] using hU

def toElement (f : ApproximableMap A B) (x : A.Element) : B.Element where
  carrier := {Y | ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y}}
  consistent := by
    intro Y hY
    obtain ⟨u, _, hrel⟩ := exists_rel_of_subset_image f x Y hY
    exact f.rel_cod hrel
  closed := by
    intro Y a hY hEnt
    obtain ⟨u, hu, hrel⟩ := exists_rel_of_subset_image f x Y hY
    have harel : f.rel u {a} :=
      f.mono hrel (proposition_2_3.iii A (f.rel_dom hrel))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz
          rw [hz]
          exact hEnt)
        (f.rel_dom hrel) (B.con_sing a)
    exact ⟨u, hu, harel⟩

@[simp] theorem mem_toElement (f : ApproximableMap A B) (x : A.Element) {Y : β} :
    Y ∈ (f.toElement x).carrier ↔ ∃ u : Finset α, ↑u ⊆ x.carrier ∧ f.rel u {Y} :=
  Iff.rfl

theorem toElement_mono (f : ApproximableMap A B) {x y : A.Element} (hxy : x ≤ y) :
    f.toElement x ≤ f.toElement y := by
  intro Y ⟨u, hu, hrel⟩
  exact ⟨u, fun z hz => hxy (hu hz), hrel⟩

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
