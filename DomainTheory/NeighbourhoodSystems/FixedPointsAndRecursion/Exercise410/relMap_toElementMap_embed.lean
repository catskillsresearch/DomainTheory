module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap















/-- The restriction `f'` has the same action as `f`: `embed a (f'(g)) = f(embed a g)`. -/
theorem relMap_toElementMap_embed (f : ApproximableMap V V) {a : V.Element}
    (ha : f.toElementMap a = a) (g : (relSystem a).Element) :
    embed a ((relMap f ha).toElementMap g) = f.toElementMap (embed a g) := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, ⟨U, hgU, haU, hUW⟩, hWX⟩
    -- `U ∈ g`, `U f W`, `W ⊆ X`; so `X ∈ f(embed g)` via the member `U` of `embed g`.
    refine ⟨U, ⟨a.sub haU, U, haU, hgU, subset_rfl⟩, ?_⟩
    exact f.mono hUW subset_rfl hWX (a.sub haU) hVX
  · rintro ⟨U, ⟨hVU, W, haW, hgW, hWU⟩, hUX⟩
    -- `W ∈ g`, `W ⊆ U`, `U f X`; so `W f X` and `X ∈ embed a (f'(g))`.
    have hVX : V.mem X := f.rel_cod hUX
    have hWX : f.rel W X := f.mono hUX hWU subset_rfl (a.sub haW) hVX
    have haX : a.mem X := by
      have hpr : V.principal (a.sub haW) ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haW hVZ hXZ
      have hmemfW : (f.toElementMap (V.principal (a.sub haW))).mem X :=
        (f.rel_iff_mem_principal (a.sub haW)).mp hWX
      have := (f.toElementMap_mono hpr) X hmemfW
      rw [ha] at this; exact this
    exact ⟨hVX, X, haX, ⟨W, hgW, haW, hWX⟩, subset_rfl⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
