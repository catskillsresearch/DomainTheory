/-ai
Scott 1976, Theorem 1.3, composition. The composite of two Scott-continuous endomaps of Pω is Scott continuous.

Fix an argument and compare membership of a code. If the code lies in the composite, Theorem 1.1 applied to the outer map yields a finite witness contained in the inner image, and Theorem 1.1 applied to the inner map yields a finite witness contained in the argument. Monotonicity of the outer map places the code in the composite at that finite set, which is membership in the Scott union. The converse inclusion is monotonicity of the outer map along monotonicity of the inner map.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3, composition.** -/
theorem theorem_1_3_comp {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (f ∘ g) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    have hk' : k ∈ f (g x) := hk
    have := (theorem_1_1 f).mp hf (g x) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (g x) := by
      simpa [e_pow2, Set.singleton_subset_iff] using hk'
    obtain ⟨m, hm, hkm⟩ := this.mp hfin
    have := (theorem_1_1 g).mp hg x m
    obtain ⟨n, hn, hmn⟩ := this.mp hm
    refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
    have : e (2 ^ k) ⊆ f (g (e n)) :=
      subset_trans hkm (isScottContinuous_monotone hf hmn)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact isScottContinuous_monotone hf (isScottContinuous_monotone hg hn) hkn

end DomainTheory.DataTypesAsLattices
