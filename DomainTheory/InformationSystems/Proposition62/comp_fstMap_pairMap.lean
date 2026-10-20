/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Product
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition62.Basic
import DomainTheory.InformationSystems.Proposition62.fstFinset_liftLeft
import DomainTheory.InformationSystems.Proposition62.sndFinset_liftLeft
import DomainTheory.InformationSystems.Proposition62.ProdCon_liftLeft


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
