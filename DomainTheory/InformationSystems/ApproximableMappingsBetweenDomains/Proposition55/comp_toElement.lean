/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}


/-- **Proposition 5.5(ii).** `(g ∘ f)(x) = g(f(x))`. -/
theorem comp_toElement (g : ApproximableMap B C) (f : ApproximableMap A B) (x : A.Element) :
    (comp g f).toElement x = g.toElement (f.toElement x) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨v, hf, hg⟩⟩
    -- Z ∈ g(f(x)): need ∃ v' ⊆ f(x), v' g {Z}. Have v with u f v and v g {Z}?
    -- hg : g.rel v w where w should be {Z}. Our rel is to w = {Z} from toElement def.
    -- Actually ⟨u, hu, hrel⟩ where hrel : ∃ v, f.rel u v ∧ g.rel v {Z}
    refine ⟨v, ?_, hg⟩
    intro b hb
    -- b ∈ v ⇒ need b ∈ f(x). Since u f v and u ⊆ x, use: u f {b} by mono, so b ∈ f(x).
    have hb' : b ∈ v := Finset.mem_coe.1 hb
    have hsing : f.rel u {b} :=
      f.mono hf (proposition_2_3_iii A (f.rel_dom hf))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz; subst hz
          exact B.ent_refl (f.rel_cod hf) hb')
        (f.rel_dom hf) (B.con_sing b)
    exact ⟨u, hu, hsing⟩
  · intro Z ⟨v, hv, hg⟩
    -- Z ∈ g(f(x)) with v ⊆ f(x), v g {Z}.
    -- Need u ⊆ x with u (g∘f) {Z}. From v ⊆ f(x), get u with u f v (exists_rel).
    obtain ⟨u, hu, hf⟩ := exists_rel_of_subset_image f x v hv
    exact ⟨u, hu, ⟨v, hf, hg⟩⟩

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
