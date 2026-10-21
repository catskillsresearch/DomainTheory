/-ai
Embedding the image of a relativized filter under the restriction of f equals the image under f of the embedding of that filter.

Extensionality compares membership of a neighbourhood X. In one direction, membership in the embedded image supplies a neighbourhood of the filter related by f to a set contained in X; that neighbourhood belongs to the embedding, and monotonicity of the relation of f puts X in the image of the embedding. In the other direction, membership in the image of the embedding supplies a neighbourhood of the embedding related by f to X, and its witness yields a relation from a neighbourhood of the filter to X. The same comparison of the principal element with a used for the codomain of the restriction shows that X belongs to a, so X belongs to the embedded image of the restricted map.
ai-/
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
