/-ai
Any Scott-continuous map that agrees along an embedding with a given map out of the subspace lies below the canonical Scott extension of that map.

Expand the competing map as the supremum of its infima over the open neighbourhoods of the point. Each such infimum lies below the infimum of the original map on the preimage of the neighbourhood, because the two maps agree along the embedding, and that infimum is a term of the extension.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.continuous_eq_sSup_openInfs

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]


omit [TopologicalSpace X] in
/-- **Maximality clause of Scott 1972, Proposition 3.8.** Any continuous solution `f'` of
`f' ∘ e = f` lies below `scottExtend e f`. Following Scott: expand `f'` via
`continuous_eq_sSup_openInfs`, restrict each meet from `U` to the embedded subspace `e(X) ∩ U`
(only enlarging the meet), and recognize the result as a defining term of `scottExtend`. -/
theorem scottExtend_maximal (hE : ContinuousLattice E) (e : X → Y) {f : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    f' y ≤ scottExtend e f y := by
  rw [continuous_eq_sSup_openInfs hE hf' y]
  refine sSup_le ?_
  rintro d ⟨U, hUo, hyU, rfl⟩
  refine le_trans ?_ (le_sSup ⟨U, hUo, hyU, rfl⟩)
  refine le_sInf ?_
  rintro w ⟨x, hxU, rfl⟩
  rw [← h_ext x]
  exact sInf_le ⟨e x, hxU, rfl⟩

end InjectiveExtension
end DomainTheory.ContinuousLattice
