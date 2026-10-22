module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*}


/-- **Exercise 7.20 — the relation of `union` at the level of `ℙℙ𝒟`/`ℙ𝒟`-codes.** For any
presentation `Q` of `ℙ𝒟` whose `c`-th neighbourhood is `Y_c = ⋃_{a∈dl c} ↓Xₐ` (e.g. the
`PDPresentation` of Proposition 7.10), and the canonical enumeration `(ℙℙ𝒟).Ypd Q` of `ℙℙ𝒟`,
`(union).rel ((ℙℙ𝒟).Ypd Q n) (ℙ𝒟.Ypd P m) ↔ ∀ c ∈ dl n, ∀ a ∈ dl c, ∃ b ∈ dl m, Xₐ ⊆ X_b`. -/
theorem unionMap_rel_Ypd_iff {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (Q : ComputablePresentation V.PowerDomain) (hQ : ∀ c, Q.X c = V.Ypd P c) {n m : ℕ} :
    (unionMap V).rel (V.PowerDomain.Ypd Q n) (V.Ypd P m)
      ↔ ∀ c ∈ decodeList n, ∀ a ∈ decodeList c, ∃ b ∈ decodeList m, P.X a ⊆ P.X b := by
  constructor
  · rintro ⟨-, -, hbody⟩ c hc a ha
    have hSmem : Q.X c ∈ V.PowerDomain.Ypd Q n :=
      (V.PowerDomain.mem_Ypd Q).mpr ⟨c, hc, Q.mem_X c, subset_rfl⟩
    have hXinS : P.X a ∈ Q.X c := by
      rw [hQ c]; exact (V.mem_Ypd P).mpr ⟨a, ha, P.mem_X a, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody (Q.X c) hSmem (P.X a) hXinS
    obtain ⟨b, hb, hYin⟩ := (V.mem_Ypd P).mp hYB
    exact ⟨b, hb, hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨V.PowerDomain.Ypd_isPDmem Q n, V.Ypd_isPDmem P m, ?_⟩
    intro S hS X hX
    obtain ⟨c, hc, hScod⟩ := (V.PowerDomain.mem_Ypd Q).mp hS
    have hXinQ : X ∈ Q.X c := hScod.2 hX
    rw [hQ c] at hXinQ
    obtain ⟨a, ha, hXin⟩ := (V.mem_Ypd P).mp hXinQ
    obtain ⟨b, hb, hab⟩ := hgen c hc a ha
    exact ⟨P.X b, (V.mem_Ypd P).mpr ⟨b, hb, P.mem_X b, subset_rfl⟩, hXin.2.trans hab⟩

end DomainTheory.NeighbourhoodSystems
