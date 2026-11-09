module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.entSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.inlMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.inrMap
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

namespace entSet

theorem u_of_inl_witness {u u' : Finset (SumToken α β)} {v : Finset α}
    (hlne : lftFinset u ≠ ∅) (hinl : (inlMap A B).rel v u')
    (huv : A.EntSet (lftFinset u) v) (hu : SumCon A B u)
    (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hv, hu', hr', hEnt⟩ := hinl
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u' := (mem_lftFinset).2 hp
    have hAx : A.Ent v x := hEnt x hx
    have hAx' : A.Ent (lftFinset u) x :=
      A.ent_trans (SumCon.lft_mem_of_rht_empty A B hu hr) hv huv hAx
    exact ⟨hu, ⟨hlne, hAx'⟩⟩
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
      rw [hr'] at this; exact Finset.notMem_empty _ this)

theorem u_of_inr_witness {u u' : Finset (SumToken α β)} {w : Finset β}
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
      B.ent_trans (SumCon.rht_mem_of_lft_empty A B hu hl) hw huw hBy
    exact ⟨hu, ⟨hrne, hBy'⟩⟩
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u' := (mem_lftFinset).2 hp
      rw [hl'] at this; exact Finset.notMem_empty _ this)

end entSet

namespace ApproximableMap

variable {C : InfoSys γ}

theorem copairMap.union_disj (f : ApproximableMap A C) (g : ApproximableMap B C)
    {u : Finset (SumToken α β)} {s s' : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hs' : s' ∈ C.Con)
    (h : C.EntSet ∅ s ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
    (h' : C.EntSet ∅ s' ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s') ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s')) :
    C.EntSet ∅ (s ∪' s') ∨
      (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) (s ∪' s')) ∨
        (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) (s ∪' s')) := by
  rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩ <;> rcases h' with h' | ⟨hne', hf'⟩ | ⟨hne', hg'⟩
  · exact Or.inl (proposition_2_3.vi (sys := C) h h')
  · have hf0 : f.rel (lftFinset u) s :=
      f.mono f.empty_rel (EntSet.empty A _) h
        (SumCon.lft_con_of_lft_nonempty A B hu hne') hs
    exact Or.inr (Or.inl ⟨hne', f.union_right hf0 hf'⟩)
  · have hg0 : g.rel (rhtFinset u) s :=
      g.mono g.empty_rel (EntSet.empty B _) h
        (SumCon.rht_con_of_rht_nonempty A B hu hne') hs
    exact Or.inr (Or.inr ⟨hne', g.union_right hg0 hg'⟩)
  · have hf0 : f.rel (lftFinset u) s' :=
      f.mono f.empty_rel (EntSet.empty A _) h'
        (SumCon.lft_con_of_lft_nonempty A B hu hne) hs'
    exact Or.inr (Or.inl ⟨hne, f.union_right hf hf0⟩)
  · exact Or.inr (Or.inl ⟨hne, f.union_right hf hf'⟩)
  · exact False.elim (hne' (SumCon.rht_empty_of_lft_nonempty A B hu hne))
  · have hg0 : g.rel (rhtFinset u) s' :=
      g.mono g.empty_rel (EntSet.empty B _) h'
        (SumCon.rht_con_of_rht_nonempty A B hu hne) hs'
    exact Or.inr (Or.inr ⟨hne, g.union_right hg hg0⟩)
  · exact False.elim (hne' (SumCon.lft_empty_of_rht_nonempty A B hu hne))
  · exact Or.inr (Or.inr ⟨hne, g.union_right hg hg'⟩)

def copairMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    ApproximableMap (sumSystem A B) C where
  rel u s :=
    SumCon A B u ∧ s ∈ C.Con ∧
      (C.EntSet ∅ s ∨
        (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
          (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨SumCon_empty A B, C.con_empty, Or.inl (EntSet.empty C ∅)⟩
  union_right := by
    rintro u s s' ⟨hu, hs, h⟩ ⟨_, hs', h'⟩
    have hU := copairMap.union_disj A B f g hu hs hs' h h'
    refine ⟨hu, ?_, hU⟩
    rcases hU with hE | ⟨_, hf⟩ | ⟨_, hg⟩
    · exact C.con_subset (proposition_2_3.ii (sys := C) C.con_empty hE)
        (funion.subset_right _ _)
    · exact f.rel_cod hf
    · exact g.rel_cod hg
  mono := by
    rintro u u' s s' ⟨hu, hs, h⟩ hEntu hEnts hu' hs'
    refine ⟨hu', hs', ?_⟩
    rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · exact Or.inl (proposition_2_3.iv (sys := C) C.con_empty hs h hEnts)
    · have hne' : lftFinset u' ≠ ∅ := by
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_lftFinset).1 hx)).2.1
      exact Or.inr (Or.inl ⟨hne',
        f.mono hf (entSet.lft_of_sumEntSet A B hEntu) hEnts
          (SumCon.lft_con_of_lft_nonempty A B hu' hne') hs'⟩)
    · have hne' : rhtFinset u' ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_rhtFinset).1 hy)).2.1
      exact Or.inr (Or.inr ⟨hne',
        g.mono hg (entSet.rht_of_sumEntSet A B hEntu) hEnts
          (SumCon.rht_con_of_rht_nonempty A B hu' hne') hs'⟩)

namespace copairMap

theorem botElement (f : ApproximableMap A C) (g : ApproximableMap B C) :
    (copairMap A B f g).toElement (sumSystem A B).botElement = C.botElement := by
  apply le_antisymm
  · intro Y ⟨u, hu, ⟨huCon, hs, hcop⟩⟩
    have onlyBot : ∀ p ∈ u, p = SumToken.bot (α := α) (β := β) := by
      intro p hp
      have hEnt : (sumSystem A B).Ent {sumBot} p := hu (Finset.mem_coe.2 hp)
      cases p with
      | bot => rfl
      | left x =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : lftFinset ({sumBot} : Finset (SumToken α β)) = ∅ := lftFinset.singleton_bot
          exact hne this)
      | right y =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : rhtFinset ({sumBot} : Finset (SumToken α β)) = ∅ := rhtFinset.singleton_bot
          exact hne this)
    have hl : lftFinset u = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch onlyBot _ ((mem_lftFinset).1 hx))
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    have hr : rhtFinset u = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch onlyBot _ ((mem_rhtFinset).1 hy))
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    rcases hcop with hE | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact C.ent_trans (C.con_sing C.bot) C.con_empty
        (fun _ hz => False.elim (Finset.notMem_empty _ hz))
        (hE Y (Finset.mem_singleton_self _))
    · exact False.elim (hne hl)
    · exact False.elim (hne hr)
  · intro Y hY
    refine ⟨∅, fun _ hp => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hp)), ?_⟩
    refine ⟨SumCon_empty A B, C.con_sing Y, Or.inl ?_⟩
    intro Z hZ
    have : Z = Y := Finset.mem_singleton.mp hZ
    subst this
    exact C.ent_trans C.con_empty (C.con_sing C.bot)
      (fun _ hz => by
        have : _ = C.bot := Finset.mem_singleton.mp hz
        subst this
        exact C.ent_bot C.con_empty)
      hY

theorem comp_inl (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inlMap A B) = f := by
  refine ApproximableMap.ext fun v s => ?_
  constructor
  · rintro ⟨u, ⟨hv, hu, hr, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨_, hf⟩ | ⟨hne, _⟩
    · exact f.mono f.empty_rel (EntSet.empty A v) hE hv hs
    · exact f.mono hf hEnt (proposition_2_3.iii C hs) hv hs
    · exact False.elim (hne hr)
  · intro hf
    let vBot := insert A.bot v
    have hvBot : vBot ∈ A.Con := A.ent_con (A.ent_bot (f.rel_dom hf))
    have hEntBot : A.EntSet vBot v :=
      fun _ hx => A.ent_refl hvBot (Finset.mem_insert_of_mem hx)
    have hfBot : f.rel vBot s :=
      f.mono hf hEntBot (proposition_2_3.iii C (f.rel_cod hf)) hvBot (f.rel_cod hf)
    refine ⟨liftSumLeft (β := β) vBot, ?_, ?_⟩
    · refine ⟨f.rel_dom hf, liftSumLeft.con A B hvBot,
        liftSumLeft.rhtFinset_eq (β := β) vBot, ?_⟩
      rw [liftSumLeft.lftFinset_eq]
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst hx; exact A.ent_bot (f.rel_dom hf)
      · exact A.ent_refl (f.rel_dom hf) hx
    · refine ⟨liftSumLeft.con A B hvBot, f.rel_cod hf, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · rw [liftSumLeft.lftFinset_eq]; exact Finset.insert_ne_empty A.bot v
      · rw [liftSumLeft.lftFinset_eq]; exact hfBot

theorem comp_inr (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inrMap A B) = g := by
  refine ApproximableMap.ext fun w s => ?_
  constructor
  · rintro ⟨u, ⟨hw, hu, hl, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨hne, _⟩ | ⟨_, hg⟩
    · exact g.mono g.empty_rel (EntSet.empty B w) hE hw hs
    · exact False.elim (hne hl)
    · exact g.mono hg hEnt (proposition_2_3.iii C hs) hw hs
  · intro hg
    let wBot := insert B.bot w
    have hwBot : wBot ∈ B.Con := B.ent_con (B.ent_bot (g.rel_dom hg))
    have hEntBot : B.EntSet wBot w :=
      fun _ hy => B.ent_refl hwBot (Finset.mem_insert_of_mem hy)
    have hgBot : g.rel wBot s :=
      g.mono hg hEntBot (proposition_2_3.iii C (g.rel_cod hg)) hwBot (g.rel_cod hg)
    refine ⟨liftSumRight (α := α) wBot, ?_, ?_⟩
    · refine ⟨g.rel_dom hg, liftSumRight.con A B hwBot,
        liftSumRight.lftFinset_eq (α := α) wBot, ?_⟩
      rw [liftSumRight.rhtFinset_eq]
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst hy; exact B.ent_bot (g.rel_dom hg)
      · exact B.ent_refl (g.rel_dom hg) hy
    · refine ⟨liftSumRight.con A B hwBot, g.rel_cod hg, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [liftSumRight.rhtFinset_eq]; exact Finset.insert_ne_empty B.bot w
      · rw [liftSumRight.rhtFinset_eq]; exact hgBot

theorem unique (f : ApproximableMap A C) (g : ApproximableMap B C)
    (h : ApproximableMap (sumSystem A B) C)
    (hinl : comp h (inlMap A B) = f) (hinr : comp h (inrMap A B) = g)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement) :
    h = copairMap A B f g := by
  refine ApproximableMap.ext fun u s => ?_
  constructor
  · intro hh
    have hu : SumCon A B u := h.rel_dom hh
    have hs : s ∈ C.Con := h.rel_cod hh
    refine ⟨hu, hs, ?_⟩
    rcases lftFinset.eq_empty_or_mem u with hl | ⟨x0, hx0⟩
    · rcases rhtFinset.eq_empty_or_mem u with hr | ⟨y0, hy0⟩
      · exact Or.inl (entSet.empty_of_rel_bot_like A B h hbot hu hs hl hr hh)
      · have hl' : lftFinset u = ∅ := hl
        have hg : g.rel (rhtFinset u) s := by
          have hinr' : (comp h (inrMap A B)).rel (rhtFinset u) s := by
            refine ⟨liftSumRight (α := α) (rhtFinset u), ?_, ?_⟩
            · exact ⟨SumCon.rht_mem_of_lft_empty A B hu hl',
                liftSumRight.con A B (SumCon.rht_mem_of_lft_empty A B hu hl'),
                liftSumRight.lftFinset_eq (α := α) _, by
                  rw [liftSumRight.rhtFinset_eq]
                  exact proposition_2_3.iii B
                    (SumCon.rht_mem_of_lft_empty A B hu hl')⟩
            · exact h.mono hh (entSet.liftRht_of_right_only A B hu hl')
                (proposition_2_3.iii C hs)
                (liftSumRight.con A B (SumCon.rht_mem_of_lft_empty A B hu hl')) hs
          simpa [hinr] using hinr'
        exact Or.inr (Or.inr ⟨Finset.ne_empty_of_mem hy0, hg⟩)
    · have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx0
      have hr : rhtFinset u = ∅ := SumCon.rht_empty_of_lft_nonempty A B hu hne
      have hf : f.rel (lftFinset u) s := by
        have hinl' : (comp h (inlMap A B)).rel (lftFinset u) s := by
          refine ⟨liftSumLeft (β := β) (lftFinset u), ?_, ?_⟩
          · exact ⟨SumCon.lft_mem_of_rht_empty A B hu hr,
              liftSumLeft.con A B (SumCon.lft_mem_of_rht_empty A B hu hr),
              liftSumLeft.rhtFinset_eq (β := β) _, by
                rw [liftSumLeft.lftFinset_eq]
                exact proposition_2_3.iii A
                  (SumCon.lft_mem_of_rht_empty A B hu hr)⟩
          · exact h.mono hh (entSet.liftLft_of_left_only A B hu hr)
              (proposition_2_3.iii C hs)
              (liftSumLeft.con A B (SumCon.lft_mem_of_rht_empty A B hu hr)) hs
        simpa [hinl] using hinl'
      exact Or.inr (Or.inl ⟨hne, hf⟩)
  · intro hc
    rcases hc with ⟨hu, hs, hcop⟩
    rcases hcop with hE | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · have hb : h.rel ∅ s :=
        h.mono h.empty_rel (EntSet.empty (sumSystem A B) _) hE
          (sumSystem A B).con_empty hs
      exact h.mono hb (EntSet.empty (sumSystem A B) _) (proposition_2_3.iii C hs) hu hs
    · have : (comp h (inlMap A B)).rel (lftFinset u) s := by simpa [hinl] using hf
      rcases this with ⟨u', hinl', hh'⟩
      have hr : rhtFinset u = ∅ := SumCon.rht_empty_of_lft_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet.u_of_inl_witness A B hne hinl'
          (proposition_2_3.iii A (SumCon.lft_mem_of_rht_empty A B hu hr)) hu hr
      exact h.mono hh' hEnt (proposition_2_3.iii C hs) hu hs
    · have : (comp h (inrMap A B)).rel (rhtFinset u) s := by simpa [hinr] using hg
      rcases this with ⟨u', hinr', hh'⟩
      have hl : lftFinset u = ∅ := SumCon.lft_empty_of_rht_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet.u_of_inr_witness A B hne hinr'
          (proposition_2_3.iii B (SumCon.rht_mem_of_lft_empty A B hu hl)) hu hl
      exact h.mono hh' hEnt (proposition_2_3.iii C hs) hu hs

end copairMap

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
