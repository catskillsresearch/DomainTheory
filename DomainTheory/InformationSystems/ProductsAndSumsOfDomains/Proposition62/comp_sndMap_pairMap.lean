/-ai
The composite of the second projection with the pairing of approximable maps f and g equals g. Scott writes this as snd composed with the pair of f and g equals g.

Extensionality of approximable maps reduces the equation to a relation in both directions. If a product set u witnesses the composite, then g relates the source to the second projection of u and the second projection entails the target from that projection, so monotonicity of g, using proposition 2.3(iii) on the domain of the relation, yields the relation for g. Conversely, if g relates s to w, the right lift of w is a witness. Its second projection equals w, so the relation for g is unchanged, and f relates s to the first projection because monotonicity from the empty relation produces a relation to the empty set and the left-handed bottom-subset lemma enlarges the target to that projection. The lift is product-consistent because the codomain of g is consistent, and proposition 2.3(iii) in B supplies the entailment required by the second projection.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndFinset_liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstFinset_liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.ProdCon_liftRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)


namespace ApproximableMap

variable {C : InfoSys γ}


/-- `snd ∘ ⟨f, g⟩ = g`. -/
theorem comp_sndMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (sndMap A B) (pairMap A B f g) = g := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hw, hEnt⟩⟩
    exact g.mono hg (proposition_2_3_iii C (g.rel_dom hg)) hEnt (g.rel_dom hg) hw
  · intro hg
    refine ⟨liftRight A B w, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hs : s ∈ C.Con := g.rel_dom hg
        have hf0 : f.rel s (∅ : Finset α) :=
          f.mono f.empty_rel (C.entSet_empty s) (A.entSet_empty ∅) hs A.con_empty
        exact rel_bot_subset_left f hs hf0 (fstFinset_liftRight A B w)
      · rw [sndFinset_liftRight]
        exact hg
    · refine ⟨ProdCon_liftRight A B (g.rel_cod hg), g.rel_cod hg, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (g.rel_cod hg)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
