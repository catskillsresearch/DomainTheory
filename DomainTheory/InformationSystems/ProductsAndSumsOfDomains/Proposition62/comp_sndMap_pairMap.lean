/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
