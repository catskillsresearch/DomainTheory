module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem entSet_u_of_inr_witness {u u' : Finset (SumToken α β)} {w : Finset β}
    (hrne : rhtFinset u ≠ ∅) (hinr : (inrMap A B).rel w u')
    (huw : B.EntSet (rhtFinset u) w) (hu : SumCon A B u)
    (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hw, hu', hl', hEnt⟩ := hinr
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
    have hBy : B.Ent w y := hEnt y hy
    have hBy' : B.Ent (rhtFinset u) y :=
      B.ent_trans (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hw huw hBy
    exact ⟨hu, ⟨hrne, hBy'⟩⟩
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u' := (mem_lftFinset).2 hp
      rw [hl'] at this; exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
