module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_mem_Con_of_SumCon_rht_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumLftCarrier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

namespace ApproximableMap

variable {C : InfoSys γ}

/-- Left copy as an `A`-element, given some left token in `z`. -/
def sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) : A.Element where
  carrier := sumLftCarrier A B z
  consistent := by
    intro Y hY
    have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
      exact hY (Finset.mem_coe.2 hx)
    have h := lft_mem_Con_of_SumCon_rht_empty A B (z.consistent _ hsub)
      (rhtFinset_liftSumLeft (β := β) Y)
    rwa [lftFinset_liftSumLeft] at h
  closed := by
    intro Y a hY hEnt
    if hempty : Y = ∅ then
      subst hempty
      have hEnt' : A.Ent {x0} a :=
        A.ent_trans (A.con_sing x0) A.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.left x0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .left x0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hx0
      have hSum : (sumSystem A B).Ent {SumToken.left x0} (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [lftFinset_singleton_left]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
        exact hY (Finset.mem_coe.2 hx)
      have hSum : (sumSystem A B).Ent (liftSumLeft (β := β) Y) (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [lftFinset_liftSumLeft]; exact hempty
        · rw [lftFinset_liftSumLeft]; exact hEnt
      exact z.closed _ _ hsub hSum

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
