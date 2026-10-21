/-ai
Under the correspondence of a function space with its approximable maps, the combinator sends the point named by a map f to the point named by the power-domain action of f.

Elements agree when they contain the same neighbourhoods. A neighbourhood of the image contains the power-domain action of f because f belongs to the witnessing source neighbourhood. Conversely, from membership of that action in a step neighbourhood, a finite list of steps is gathered so that every map agreeing with f on the list again has its power-domain action in the target, and the step neighbourhood of that list is a neighbourhood of f.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.exists_stepFun_forall_PFmap_rel

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems
