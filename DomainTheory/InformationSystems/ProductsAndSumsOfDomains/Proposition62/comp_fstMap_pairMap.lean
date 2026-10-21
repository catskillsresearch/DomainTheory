/-ai
The composite of the first projection with the pairing of approximable maps f and g equals f. Scott writes this as fst composed with the pair of f and g equals f.

Extensionality of approximable maps reduces the equation to a relation in both directions. If a product set u witnesses the composite, then f relates the source to the first projection of u and the first projection entails the target from that projection, so monotonicity of f, using proposition 2.3(iii) on the domain of the relation, yields the relation for f. Conversely, if f relates s to v, the left lift of v is a witness. Its first projection equals v, so the relation for f is unchanged, and g relates s to the second projection because monotonicity from the empty relation produces a relation to the empty set and the bottom-subset lemma enlarges the target to that projection. The lift is product-consistent because the codomain of f is consistent, and proposition 2.3(iii) in A supplies the entailment required by the first projection.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstFinset_liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndFinset_liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.ProdCon_liftLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)


namespace ApproximableMap

variable {C : InfoSys γ}


/-- `fst ∘ ⟨f, g⟩ = f`. -/
theorem comp_fstMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (fstMap A B) (pairMap A B f g) = f := by
  refine ApproximableMap.ext fun s v => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hv, hEnt⟩⟩
    exact f.mono hf (proposition_2_3_iii C (f.rel_dom hf)) hEnt (f.rel_dom hf) hv
  · intro hf
    refine ⟨liftLeft A B v, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [fstFinset_liftLeft]
        exact hf
      · have hs : s ∈ C.Con := f.rel_dom hf
        have hg0 : g.rel s (∅ : Finset β) :=
          g.mono g.empty_rel (C.entSet_empty s) (B.entSet_empty ∅) hs B.con_empty
        exact rel_bot_subset g hs hg0 (sndFinset_liftLeft A B v)
    · refine ⟨ProdCon_liftLeft A B (f.rel_cod hf), f.rel_cod hf, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (f.rel_cod hf)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
