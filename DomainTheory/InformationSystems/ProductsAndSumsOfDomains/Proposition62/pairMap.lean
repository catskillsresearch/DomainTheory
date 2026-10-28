module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_fst_of_prodEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_snd_of_prodEntSet

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
    · exact f.mono hf hEnts (entSet_fst_of_prodEntSet A B hEntu) hs' hu'.1
    · exact g.mono hg hEnts (entSet_snd_of_prodEntSet A B hEntu) hs' hu'.2

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
