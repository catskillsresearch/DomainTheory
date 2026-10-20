/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_step_of_rel

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)














namespace ApproximableMap




/-- **Theorem 7.3(ii).** `f(fix(f)) ⊆ fix(f)`. -/
theorem toElement_fixElement_le (f : ApproximableMap A A) :
    f.toElement (fixElement A f) ≤ fixElement A f := by
  intro a ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨hwCon, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  -- v0 entails u, and f.rel u {a}; mono to get f.rel v0 {a} after adjusting
  have hv0C := fixReach_con A hv0
  have huC : u ∈ A.Con := f.rel_dom hrel
  have hrel' : f.rel v0 {a} :=
    f.mono hrel hEnt
      (proposition_2_3_iii A (f.rel_cod hrel)) hv0C (f.rel_cod hrel)
  obtain ⟨n, hn⟩ := hv0
  obtain ⟨w', hw', hw'Con, hchain⟩ := fixChain_step_of_rel A f hw hn hrel'
  refine ⟨w', hw', ⟨hw'Con, A.con_sing a, {a}, ⟨n + 1, hchain⟩, ?_⟩⟩
  exact proposition_2_3_iii A (A.con_sing a)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
