module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumElement
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

namespace entSet

theorem lft_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    A.EntSet (lftFinset u) (lftFinset u') := fun _ hx =>
  (hEnt _ ((mem_lftFinset).1 hx)).2.2

theorem rht_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    B.EntSet (rhtFinset u) (rhtFinset u') := fun _ hy =>
  (hEnt _ ((mem_rhtFinset).1 hy)).2.2

theorem lft_eq_empty {u u' : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    lftFinset u' = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((hEnt _ ((mem_lftFinset).1 hx)).2.1 hl)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rht_eq_empty {u u' : Finset (SumToken α β)}
    (hr : rhtFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    rhtFinset u' = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim ((hEnt _ ((mem_rhtFinset).1 hy)).2.1 hr)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem liftLft_of_left_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumLeft (β := β) (lftFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨liftSumLeft.con A B (SumCon.lft_mem_of_rht_empty A B hu hr), trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
    refine ⟨liftSumLeft.con A B (SumCon.lft_mem_of_rht_empty A B hu hr), ⟨?_, ?_⟩⟩
    · rw [liftSumLeft.lftFinset_eq]; exact Finset.ne_empty_of_mem hx
    · rw [liftSumLeft.lftFinset_eq]
      exact A.ent_refl (SumCon.lft_mem_of_rht_empty A B hu hr) hx
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      rw [hr] at this
      exact Finset.notMem_empty _ this)

theorem liftRht_of_right_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumRight (α := α) (rhtFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨liftSumRight.con A B (SumCon.rht_mem_of_lft_empty A B hu hl), trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
    refine ⟨liftSumRight.con A B (SumCon.rht_mem_of_lft_empty A B hu hl), ⟨?_, ?_⟩⟩
    · rw [liftSumRight.rhtFinset_eq]; exact Finset.ne_empty_of_mem hy
    · rw [liftSumRight.rhtFinset_eq]
      exact B.ent_refl (SumCon.rht_mem_of_lft_empty A B hu hl) hy
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp
      rw [hl] at this
      exact Finset.notMem_empty _ this)

theorem empty_of_rel_bot_like {C : InfoSys γ} (h : ApproximableMap (sumSystem A B) C)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement)
    {u : Finset (SumToken α β)} {s : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅)
    (hh : h.rel u s) : C.EntSet ∅ s := by
  have hsub := subset_botElement_of_projections_empty A B hl hr
  have hcl : (sumSystem A B).closure u hu ≤ (sumSystem A B).botElement := by
    intro p hp
    exact (sumSystem A B).botElement.closed u p hsub hp
  have hle : C.closure s hs ≤ C.botElement := by
    have := (h.rel_iff_closure_le hu hs).1 hh
    have := le_trans this (toElement_mono h hcl)
    rwa [hbot] at this
  intro Y hY
  have hY' : Y ∈ (C.closure s hs).carrier := closure.subset C hs hY
  have hbotY : Y ∈ C.botElement.carrier := hle hY'
  exact C.ent_trans C.con_empty (C.con_sing C.bot)
    (fun _ hz => by
      have : _ = C.bot := Finset.mem_singleton.mp hz
      subst this; exact C.ent_bot C.con_empty)
    hbotY

end entSet

end InfoSys

end DomainTheory.InformationSystems
