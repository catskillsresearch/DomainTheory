/-ai
The image of an element under an approximable mapping, in the sense of Definition 5.2, is the element whose tokens are those for which some finite set contained in the given element is related to the corresponding singleton. A finite subset of this carrier is consistent because the subset-image lemma supplies a finite set related to it, and the codomain of a related pair is consistent. If such a finite set entails a further token, monotonicity, using reflexivity of entailment on the domain side and that entailment on the codomain side, replaces the related set by the singleton of the entailed token.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.exists_rel_of_subset_image

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- **Definition 5.2.** Image of an element under an approximable mapping. -/
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
      f.mono hrel (proposition_2_3_iii A (f.rel_dom hrel))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz
          rw [hz]
          exact hEnt)
        (f.rel_dom hrel) (B.con_sing a)
    exact ⟨u, hu, harel⟩

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
