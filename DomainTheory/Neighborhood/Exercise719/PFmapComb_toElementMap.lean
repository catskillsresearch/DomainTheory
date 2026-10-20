/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise719.Basic
public import DomainTheory.Neighborhood.Exercise719.exists_stepFun_forall_PFmap_rel

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}








/-- **Exercise 7.19 — faithfulness of `PFmapComb`.** Under the function-space correspondence of
Theorem 3.10 (`toFilter f` is the point of `(D → E)` fixed by `f`), `PFmapComb` really does send
`f` to `ℙf`, at **every** `f` — not merely the finite/principal points. The forward direction is
immediate; the backward direction is where the work is: given `ℙf ∈ Ψ`, `exists_stepFun_forall_PFmap_rel`
manufactures a finite neighbourhood `stepFun M ∋ f` all of whose members `g` already satisfy `ℙg ∈ Ψ`,
i.e. `Ψ` is reached from a genuine (finite) neighbourhood of `f`, exactly as continuity demands. -/
theorem PFmapComb_toElementMap (f : ApproximableMap V W) :
    (PFmapComb V W).toElementMap (toFilter f) = toFilter (PFmap f) := by
  apply Element.ext
  intro Ψ
  simp only [mem_toElementMap, mem_toFilter, PFmapComb_rel]
  constructor
  · rintro ⟨Φ, ⟨_, hΦf⟩, _, hΨmem, hbody⟩
    exact ⟨hΨmem, hbody f hΦf⟩
  · rintro ⟨hΨmem, hfΨ⟩
    obtain ⟨⟨L₂, hL₂, rfl⟩, -⟩ := hΨmem
    obtain ⟨M, hMmem, hMrel, hMgen⟩ :=
      exists_stepFun_forall_PFmap_rel f L₂ hL₂ (mem_stepFun.mp hfΨ)
    have hΦmem : (funSpace V W).mem (stepFun M) := ⟨⟨M, hMmem, rfl⟩, f, mem_stepFun.mpr hMrel⟩
    have hΨmem' : (funSpace V.PowerDomain W.PowerDomain).mem (stepFun L₂) :=
      ⟨⟨L₂, hL₂, rfl⟩, PFmap f, hfΨ⟩
    exact ⟨stepFun M, ⟨hΦmem, mem_stepFun.mpr hMrel⟩, hΦmem, hΨmem',
      fun g hg => mem_stepFun.mpr (hMgen g (mem_stepFun.mp hg))⟩

end DomainTheory.Neighborhood
