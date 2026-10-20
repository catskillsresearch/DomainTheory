/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}


/-- **Proposition 5.3(v).** `u f v` iff `v̄ ⊆ f(ū)`. -/
theorem rel_iff_closure_le (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ B.closure v hv ≤ f.toElement (A.closure u hu) := by
  constructor
  · intro hrel Y hY
    refine ⟨u, A.subset_closure hu, ?_⟩
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact hY)
      hu (B.con_sing Y)
  · intro hsub
    have hv_sub : ↑v ⊆ (f.toElement (A.closure u hu)).carrier :=
      fun y hy => hsub (B.subset_closure hv hy)
    obtain ⟨u', hu', hrel'⟩ := exists_rel_of_subset_image f (A.closure u hu) v hv_sub
    have hEnt : A.EntSet u u' := fun y hy => hu' (Finset.mem_coe.2 hy)
    exact f.mono hrel' hEnt (proposition_2_3_iii B hv) hu hv

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
