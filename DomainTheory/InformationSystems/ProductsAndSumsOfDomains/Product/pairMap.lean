module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem_more
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftRight
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55.comp

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

def pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    ApproximableMap C (productSystem A B) where
  rel s u := f.rel s (fstFinset A B u) ∧ g.rel s (sndFinset A B u)
  rel_dom h := f.rel_dom h.1
  rel_cod h := ⟨f.rel_cod h.1, g.rel_cod h.2⟩
  empty_rel := by
    rw [fstFinset.empty, sndFinset.empty]
    exact ⟨f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro s u u' ⟨hf, hg⟩ ⟨hf', hg'⟩
    rw [fstFinset.funion A B u u', sndFinset.funion A B u u']
    exact ⟨f.union_right hf hf', g.union_right hg hg'⟩
  mono := by
    rintro s s' u u' ⟨hf, hg⟩ hEnts hEntu hs' hu'
    refine ⟨?_, ?_⟩
    · exact f.mono hf hEnts (ProdEnt.entSet_fst A B hEntu) hs' hu'.1
    · exact g.mono hg hEnts (ProdEnt.entSet_snd A B hEntu) hs' hu'.2

namespace pairMap

theorem comp_fst (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (productSystem.fstMap A B) (pairMap A B f g) = f := by
  refine ApproximableMap.ext fun s v => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hv, hEnt⟩⟩
    exact f.mono hf (proposition_2_3.iii C (f.rel_dom hf)) hEnt (f.rel_dom hf) hv
  · intro hf
    refine ⟨liftLeft A B v, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [liftLeft.fstFinset_eq]
        exact hf
      · have hs : s ∈ C.Con := f.rel_dom hf
        have hg0 : g.rel s (∅ : Finset β) :=
          g.mono g.empty_rel (EntSet.empty C s) (EntSet.empty B ∅) hs B.con_empty
        exact rel_bot_subset g hs hg0 (liftLeft.sndFinset_eq A B v)
    · refine ⟨liftLeft.con A B (f.rel_cod hf), f.rel_cod hf, ?_⟩
      rw [liftLeft.fstFinset_eq]
      exact proposition_2_3.iii A (f.rel_cod hf)

theorem comp_snd (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (productSystem.sndMap A B) (pairMap A B f g) = g := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hw, hEnt⟩⟩
    exact g.mono hg (proposition_2_3.iii C (g.rel_dom hg)) hEnt (g.rel_dom hg) hw
  · intro hg
    refine ⟨liftRight A B w, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hs : s ∈ C.Con := g.rel_dom hg
        have hf0 : f.rel s (∅ : Finset α) :=
          f.mono f.empty_rel (EntSet.empty C s) (EntSet.empty A ∅) hs A.con_empty
        exact rel_bot_subset_left f hs hf0 (liftRight.fstFinset_eq A B w)
      · rw [liftRight.sndFinset_eq]
        exact hg
    · refine ⟨liftRight.con A B (g.rel_cod hg), g.rel_cod hg, ?_⟩
      rw [liftRight.sndFinset_eq]
      exact proposition_2_3.iii B (g.rel_cod hg)

theorem unique (f : ApproximableMap C A) (g : ApproximableMap C B)
    (h : ApproximableMap C (productSystem A B))
    (hfst : comp (productSystem.fstMap A B) h = f) (hsnd : comp (productSystem.sndMap A B) h = g) :
    h = pairMap A B f g :=
  (ext_iff_toElement h (pairMap A B f g)).2 fun x =>
    productSystem.element_eq_of_fst_snd A B (h.toElement x) ((pairMap A B f g).toElement x)
      (by
        have h1 : (productSystem.fstMap A B).toElement (h.toElement x) = f.toElement x := by
          rw [← comp.toElement, hfst]
        have h2 : (productSystem.fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
          rw [← comp.toElement, comp_fst]
        exact h1.trans h2.symm)
      (by
        have h1 : (productSystem.sndMap A B).toElement (h.toElement x) = g.toElement x := by
          rw [← comp.toElement, hsnd]
        have h2 : (productSystem.sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
          rw [← comp.toElement, comp_snd]
        exact h1.trans h2.symm)

end pairMap

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
