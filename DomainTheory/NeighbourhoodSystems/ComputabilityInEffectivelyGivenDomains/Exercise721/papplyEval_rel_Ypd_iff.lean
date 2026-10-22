module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}


/-- **Exercise 7.21 — `papply`'s relation at the level of `ℙ𝒟`-codes.** Over the canonical
presentations of Proposition 7.10 (function-space presentation `Pf`, domain `P`, codomain `Q`):
`papplyEval.rel (Y_Φc) (Y_Ac) (Y_Bc) ↔ ∀ g ∈ dl Φc, ∀ x ∈ dl Ac, ∃ y ∈ dl Bc, eval (Pf.X g)(P.X x)(Q.X y)`. -/
theorem papplyEval_rel_Ypd_iff {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W) {Φc Ac Bc : ℕ} :
    (papplyEval V W).rel ((funSpace V W).Ypd Pf Φc) (V.Ypd P Ac) (W.Ypd Q Bc)
      ↔ ∀ g ∈ decodeList Φc, ∀ x ∈ decodeList Ac, ∃ y ∈ decodeList Bc,
          (eval V W).rel (Pf.X g) (P.X x) (Q.X y) := by
  constructor
  · rintro ⟨-, -, -, hbody⟩ g hg x hx
    have hGin : Pf.X g ∈ (funSpace V W).Ypd Pf Φc :=
      ((funSpace V W).mem_Ypd Pf).mpr ⟨g, hg, Pf.mem_X g, subset_rfl⟩
    have hXin : P.X x ∈ V.Ypd P Ac := (V.mem_Ypd P).mpr ⟨x, hx, P.mem_X x, subset_rfl⟩
    obtain ⟨Y, hYin, hrel⟩ := hbody (Pf.X g) hGin (P.X x) hXin
    obtain ⟨b, hb, hYmem, hYsub⟩ := (W.mem_Ypd Q).mp hYin
    exact ⟨b, hb, (eval V W).mono hrel subset_rfl subset_rfl hYsub
      ((eval V W).rel_dom₀ hrel) ((eval V W).rel_dom₁ hrel) (Q.mem_X b)⟩
  · intro hgen
    refine ⟨(funSpace V W).Ypd_isPDmem Pf Φc, V.Ypd_isPDmem P Ac, W.Ypd_isPDmem Q Bc, ?_⟩
    intro G hGin X hXin
    obtain ⟨g, hg, hGmem, hGsub⟩ := ((funSpace V W).mem_Ypd Pf).mp hGin
    obtain ⟨x, hx, hXmem, hXsub⟩ := (V.mem_Ypd P).mp hXin
    obtain ⟨y, hy, hrel⟩ := hgen g hg x hx
    exact ⟨Q.X y, (W.mem_Ypd Q).mpr ⟨y, hy, Q.mem_X y, subset_rfl⟩,
      (eval V W).mono hrel hGsub hXsub subset_rfl hGmem hXmem (Q.mem_X y)⟩

end DomainTheory.NeighbourhoodSystems
