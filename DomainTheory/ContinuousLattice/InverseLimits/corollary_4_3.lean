/-ai
Given Scott maps from the levels of an ω-system into a complete lattice that commute with the inclusions, there is a unique Scott map from the inverse limit that recovers each component by composition with the embedding of that level. It sends a compatible sequence to the supremum of the component values.

The mediating map preserves directed suprema, so it is a Scott map, and factorization through the embeddings recovers the components. Another Scott map with the same factorizations agrees with it at a compatible sequence because that sequence is the supremum of the embeddings of its coordinates, the family of those embeddings is nonempty and directed, and the map preserves that supremum.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_family_directed
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_eq_iSup
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf_comp_embInf
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf_preservesDirectedSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


variable {D' : Type*} [CompleteLattice D']


/-- **Scott 1972, Corollary 4.3.** Within complete lattices, `D_∞` is also the *direct* limit of
the `Dₙ` along the embeddings `iₙ`: for every compatible cocone `fₙ : Dₙ → D'` (continuous, with
`fₙ = f_{n+1} ∘ iₙ`) there is a **unique** continuous `f∞ : D_∞ → D'` with `fₙ = f∞ ∘ i_{n∞}`,
namely `f∞(x) = ⨆ₙ fₙ(xₙ)`. -/
theorem corollary_4_3 (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) :
    ∃! g : ScottMap (InverseLimit D P) D', ∀ n x, f n x = g (embInf D P n x) := by
  refine ⟨⟨coconeInf D P f,
    continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)⟩, ?_, ?_⟩
  · exact fun n x => (coconeInf_comp_embInf D P f hf n x).symm
  · intro g hg
    ext x
    -- `g x = f∞ x`, since `x = ⨆ₙ i_{n∞}(xₙ)` and `g` is continuous on this directed family
    calc g x = g (⨆ n, embInf D P n (x.1 n)) := by rw [← inverseLimit_eq_iSup D P x]
      _ = g (sSup (Set.range fun n => embInf D P n (x.1 n))) := by rw [sSup_range]
      _ = sSup (g '' Set.range fun n => embInf D P n (x.1 n)) :=
          g.preservesDirectedSup_coe _ (Set.range_nonempty _) (embInf_family_directed D P x)
      _ = ⨆ n, g (embInf D P n (x.1 n)) := by rw [← Set.range_comp, sSup_range]; rfl
      _ = ⨆ n, f n (x.1 n) := by simp_rw [← hg]

end InverseLimit
end DomainTheory.ContinuousLattice
