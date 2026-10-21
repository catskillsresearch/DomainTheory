/-ai
On the canonical power-domain codes, the power-domain action relates the neighbourhood coded by c to the neighbourhood coded by d exactly when every index in the list coded by c is related by the map to some index in the list coded by d.

A coded generator is a member of the source, so the relation supplies a target neighbourhood, which lies under a generator of the target code, and monotonicity of the map passes to the codes. Conversely, a member of the source lies under a generator, the hypothesis supplies a related code, and monotonicity extends the relation from that generator to the member.
ai-/
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
