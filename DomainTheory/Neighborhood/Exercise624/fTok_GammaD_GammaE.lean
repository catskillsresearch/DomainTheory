/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB
import DomainTheory.Neighborhood.Exercise624.Basic
import DomainTheory.Neighborhood.Exercise624.nil_mem_fTok
import DomainTheory.Neighborhood.Exercise624.fTok_mono
import DomainTheory.Neighborhood.Exercise624.mem_fTok_iUnion
import DomainTheory.Neighborhood.Exercise624.pIter_fst_subset_GammaD
import DomainTheory.Neighborhood.Exercise624.pIter_snd_subset_GammaE


namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise624












/-- **First equation of the double fixed point:** `fTok Γ_D Γ_E = Γ_D`, i.e. `tok(D + (D×E)) = Γ_D`
for `D = {Γ_D}`, `E = {Γ_E}`. -/
theorem fTok_GammaD_GammaE : fTok GammaD GammaE = GammaD := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_fTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_fTok _ _
    | succ m =>
        exact fTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

end Exercise624
end DomainTheory.Neighborhood
