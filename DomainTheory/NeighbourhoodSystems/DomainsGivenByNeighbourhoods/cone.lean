module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.BitDom
section

abbrev Str := List Bool

def cone (σ : Str) : Set Str := {w | σ <+: w}

namespace cone

@[simp] theorem mem {σ w : Str} : w ∈ BitDom.cone σ ↔ σ <+: w := Iff.rfl

theorem nil : BitDom.cone [] = Set.univ := by
  ext w
  simp [BitDom.cone]

theorem subset_cone {σ τ : Str} :
    BitDom.cone σ ⊆ BitDom.cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (List.prefix_rfl : σ <+: σ)
  · intro hτσ w hw
    exact hτσ.trans hw

theorem trichotomy (σ τ : Str) :
    BitDom.cone σ ⊆ BitDom.cone τ ∨ BitDom.cone τ ⊆ BitDom.cone σ ∨
      BitDom.cone σ ∩ BitDom.cone τ = ∅ := by
  if hστ : σ <+: τ then
    exact Or.inr (Or.inl (subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then
    exact Or.inl (subset_cone.mpr hτσ)
  else
    refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, mem, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h

theorem injective {σ τ : Str} (h : BitDom.cone σ = BitDom.cone τ) : σ = τ := by
  have h1 : τ <+: σ := subset_cone.mp (h.symm ▸ subset_rfl)
  have h2 : σ <+: τ := subset_cone.mp (h ▸ subset_rfl)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

end cone

end

end DomainTheory.NeighbourhoodSystems.BitDom
end
