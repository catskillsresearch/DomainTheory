/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Approximable
import DomainTheory.InformationSystems.Factoid45

/-!
# Factoid 4.6 — Scott topology and continuous maps

**Factoid 4.6 (Scott §4).** Basic opens `[u] = {x | u ⊆ x}` form a neighborhood basis;
`|A|` is `T₀`. Approximable maps induce Scott-continuous functions on elements, and
conversely every Scott-continuous map arises from an approximable relation
(`u f v ↔ ↑v ⊆ f(ū)`).
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Scott §4.** Basic open `[u] = {x ∈ |A| | u ⊆ x}`. -/
def basicOpen (A : InfoSys α) (u : Finset α) : Set A.Element :=
  {x | ↑u ⊆ x.carrier}

/-- Image of a nonempty set under a function is nonempty. -/
theorem nonempty_image {X Y : Type*} {S : Set X} (hne : S.Nonempty) (f : X → Y) :
    (f '' S).Nonempty :=
  hne.image f

/-- Monotone images preserve directedness. -/
theorem directed_image {A : InfoSys α} {B : InfoSys β} {S : Set A.Element}
    (hdir : A.IsDirected S) (f : A.Element → B.Element)
    (hmono : ∀ {x y}, x ≤ y → f x ≤ f y) : B.IsDirected (f '' S) := by
  intro x y hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨z₀, hz₀, hxz, hyz⟩ := hdir x₀ y₀ hx₀ hy₀
  exact ⟨f z₀, ⟨z₀, hz₀, rfl⟩, hmono hxz, hmono hyz⟩

/-- Scott-continuous map of domains: monotone and preserves directed lubs. -/
structure ScottContinuous (A : InfoSys α) (B : InfoSys β) where
  toFun : A.Element → B.Element
  mono' : ∀ {x y : A.Element}, x ≤ y → toFun x ≤ toFun y
  map_directedSup :
    ∀ (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S),
      toFun (A.directedSup S hne hdir) =
        B.directedSup (toFun '' S) (nonempty_image hne toFun)
          (directed_image hdir toFun mono')

namespace ScottContinuous

variable {A : InfoSys α} {B : InfoSys β}

theorem mono (f : ScottContinuous A B) {x y : A.Element} (h : x ≤ y) :
    f.toFun x ≤ f.toFun y :=
  f.mono' h

end ScottContinuous

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- Approximable maps preserve directed lubs (Scott continuity on elements). -/
theorem toElement_directedSup (f : ApproximableMap A B)
    (S : Set A.Element) (hne : S.Nonempty) (hdir : A.IsDirected S) :
    f.toElement (A.directedSup S hne hdir) =
      B.directedSup (f.toElement '' S) (nonempty_image hne f.toElement)
        (directed_image hdir f.toElement f.toElement_mono) := by
  refine le_antisymm ?_ ?_
  · intro Y ⟨u, hu, hrel⟩
    have huU : (u : Set α) ⊆ A.familyUnionCarrier S := by
      intro a ha
      have : a ∈ (A.directedSup S hne hdir).carrier := hu ha
      rwa [A.directedSup_carrier_eq_union S hne hdir] at this
    obtain ⟨z, hz, huZ⟩ := A.exists_mem_of_subset_directedUnion S hne hdir u huU
    have : Y ∈ (f.toElement z).carrier := ⟨u, huZ, hrel⟩
    rw [B.directedSup_carrier_eq_union]
    exact ⟨f.toElement z, ⟨z, hz, rfl⟩, this⟩
  · apply B.directedSup_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact f.toElement_mono (A.le_directedSup S hne hdir hx)

/-- **Factoid 4.6 (→).** Every approximable map is Scott-continuous on elements. -/
def toScottContinuous (f : ApproximableMap A B) : ScottContinuous A B where
  toFun := f.toElement
  mono' := f.toElement_mono
  map_directedSup := f.toElement_directedSup

/-- Relation recovered from a Scott-continuous map: `u f v ↔ ↑v ⊆ g(ū)`. -/
def ofScottContinuous (g : ScottContinuous A B) : ApproximableMap A B where
  rel u v := ∃ hu : u ∈ A.Con, v ∈ B.Con ∧ ↑v ⊆ (g.toFun (A.closure u hu)).carrier
  rel_dom := fun ⟨hu, _, _⟩ => hu
  rel_cod := fun ⟨_, hv, _⟩ => hv
  empty_rel := by
    refine ⟨A.con_empty, B.con_empty, ?_⟩
    intro b hb
    exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hb))
  union_right := by
    intro u v v' ⟨hu, hv, hsub⟩ ⟨_hu', hv', hsub'⟩
    refine ⟨hu, ?_, ?_⟩
    · have hsubUV : ↑(v ∪' v') ⊆ (g.toFun (A.closure u hu)).carrier := by
        intro b hb
        rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
        · exact hsub (Finset.mem_coe.2 h)
        · exact hsub' (Finset.mem_coe.2 h)
      exact (g.toFun (A.closure u hu)).consistent (v ∪' v') hsubUV
    · intro b hb
      rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
      · exact hsub (Finset.mem_coe.2 h)
      · exact hsub' (Finset.mem_coe.2 h)
  mono := by
    intro u u' v v' ⟨hu, hv, hsub⟩ hEntUU' hEntVV' hu' hv'
    refine ⟨hu', hv', ?_⟩
    have hclos : A.closure u hu ≤ A.closure u' hu' :=
      A.closure_le_of_entSet hu hu' hEntUU'
    intro b hb
    have hEntb : B.Ent v b := hEntVV' b hb
    have hb_in : b ∈ (g.toFun (A.closure u hu)).carrier :=
      (g.toFun (A.closure u hu)).closed v b hsub hEntb
    exact g.mono hclos hb_in
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
