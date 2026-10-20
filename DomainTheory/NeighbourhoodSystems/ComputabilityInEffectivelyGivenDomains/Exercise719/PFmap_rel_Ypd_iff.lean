/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}





/-- **Exercise 7.19 — the relation of `ℙf` at the level of `ℙ𝒟`-codes.** Over the canonical
presentations of Proposition 7.10, `(ℙf).rel (Y_c) (Y_d) ↔ ∀ a ∈ dl c, ∃ b ∈ dl d, Xₐ f Y_b`. -/
theorem PFmap_rel_Ypd_iff (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (f : ApproximableMap V W) {c d : ℕ} :
    (PFmap f).rel (V.Ypd P c) (W.Ypd Q d) ↔
      ∀ a ∈ decodeList c, ∃ b ∈ decodeList d, f.rel (P.X a) (Q.X b) := by
  constructor
  · rintro ⟨-, -, hbody⟩ a ha
    have hXin : P.X a ∈ V.Ypd P c := (V.mem_Ypd P).mpr ⟨a, ha, P.mem_X a, subset_rfl⟩
    obtain ⟨Y, hYin, hrel⟩ := hbody (P.X a) hXin
    obtain ⟨b, hb, hYmem, hYsub⟩ := (W.mem_Ypd Q).mp hYin
    exact ⟨b, hb, f.mono hrel subset_rfl hYsub (P.mem_X a) (Q.mem_X b)⟩
  · intro hgen
    refine ⟨V.Ypd_isPDmem P c, W.Ypd_isPDmem Q d, ?_⟩
    rintro X hXin
    obtain ⟨a, ha, hXmem, hXsub⟩ := (V.mem_Ypd P).mp hXin
    obtain ⟨b, hb, hrel⟩ := hgen a ha
    exact ⟨Q.X b, (W.mem_Ypd Q).mpr ⟨b, hb, Q.mem_X b, subset_rfl⟩,
      f.mono hrel hXsub subset_rfl hXmem (Q.mem_X b)⟩

end DomainTheory.NeighbourhoodSystems
