module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumBot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_mono
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_insert_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_insert_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_singleton_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_singleton_right
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset_singleton_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset_singleton_bot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumEnt
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_rht_empty_of_lft_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_lft_empty_of_rht_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_lft_con_of_lft_nonempty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon_rht_con_of_rht_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- **Definition 6.3.** The separated sum information system `A + B`. -/
def sumSystem : InfoSys (SumToken α β) where
  bot := sumBot
  Con := {u | SumCon A B u}
  Ent := SumEnt A B
  con_subset := by
    intro u v hu hv
    rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨A.con_subset hl (lftFinset_mono hv),
        Finset.Subset.antisymm (by
          intro y hy
          have : y ∈ rhtFinset u := rhtFinset_mono hv hy
          rw [hr] at this
          exact False.elim (Finset.notMem_empty y this))
          (Finset.empty_subset _)⟩
    · exact Or.inr ⟨Finset.Subset.antisymm (by
          intro x hx
          have : x ∈ lftFinset u := lftFinset_mono hv hx
          rw [hl] at this
          exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _),
        B.con_subset hr (rhtFinset_mono hv)⟩
  con_sing := by
    intro p
    cases p with
    | left x =>
      exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing x,
        by
          ext y
          constructor
          · intro hy
            have : SumToken.right y ∈ ({.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy
            exact False.elim (Finset.notMem_empty y hy)⟩
    | right y =>
      exact Or.inr ⟨by
          ext x
          constructor
          · intro hx
            have : SumToken.left x ∈ ({.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx
            exact False.elim (Finset.notMem_empty x hx),
        by rw [rhtFinset_singleton_right]; exact B.con_sing y⟩
    | bot =>
      exact Or.inl ⟨by rw [lftFinset_singleton_bot]; exact A.con_empty,
        rhtFinset_singleton_bot⟩
  ent_con := by
    intro u p ⟨hu, hEnt⟩
    cases p with
    | bot =>
      rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Or.inl ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
      · exact Or.inr ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
    | left x =>
      rcases hEnt with ⟨hne, hA⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      exact Or.inl ⟨by
          rw [lftFinset_insert_left]
          exact A.ent_con hA,
        by rw [rhtFinset_insert_left]; exact hr⟩
    | right y =>
      rcases hEnt with ⟨hne, hB⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      exact Or.inr ⟨by rw [lftFinset_insert_right]; exact hl,
        by
          rw [rhtFinset_insert_right]
          exact B.ent_con hB⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, trivial⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_⟩
    cases p with
    | bot => exact trivial
    | left x =>
      have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
      have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx
      exact ⟨hne, A.ent_refl (SumCon_lft_con_of_lft_nonempty A B hu hne) hx⟩
    | right y =>
      have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      have hne : rhtFinset u ≠ ∅ := Finset.ne_empty_of_mem hy
      exact ⟨hne, B.ent_refl (SumCon_rht_con_of_rht_nonempty A B hu hne) hy⟩
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_⟩
    cases c with
    | bot => exact trivial
    | left x =>
      rcases hEntc with ⟨_, ⟨hne, hA⟩⟩
      have hlft : ∀ y ∈ lftFinset u, A.Ent (lftFinset v) y := by
        intro y hy
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        have hEy : SumEnt A B v (.left y) := hEnts _ hp
        exact hEy.2.2
      have hne' : lftFinset v ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact A.ent_trans (SumCon_lft_con_of_lft_nonempty A B hv hne')
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hlft hA
    | right y =>
      rcases hEntc with ⟨_, ⟨hne, hB⟩⟩
      have hrht : ∀ z ∈ rhtFinset u, B.Ent (rhtFinset v) z := by
        intro z hz
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        have hEz : SumEnt A B v (.right z) := hEnts _ hp
        exact hEz.2.2
      have hne' : rhtFinset v ≠ ∅ := by
        obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact B.ent_trans (SumCon_rht_con_of_rht_nonempty A B hv hne')
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hrht hB

end InfoSys

end DomainTheory.InformationSystems
