/-ai
The first projection of the pair part of the sharp system is the approximable endomap whose relation holds between sharp neighbourhoods W and Z when Z is the master neighbourhood, or W is the pair embedding of neighbourhoods P and Q with P contained in Z. The master neighbourhood is related to itself. If either codomain in an intersection is the master neighbourhood, the intersection equals the other codomain, because every sharp neighbourhood is contained in the master neighbourhood; if both are pair forms, the two decompositions agree on the left component, that component is contained in the intersection, and the intersection is a sharp neighbourhood. For monotonicity, a smaller domain neighbourhood and a larger codomain neighbourhood are allowed. If the original codomain is the master neighbourhood, the new codomain equals it by antisymmetry. If the original domain is a pair embedding, the smaller domain cannot be the master neighbourhood, since that would force the pair embedding to equal it, and it cannot be a zero-embedding, since an empty-tagged token of that zero-embedding would belong to the pair embedding. The smaller domain is therefore a pair whose left component is contained in the original left component and hence in the larger codomain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.inSharpMap_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **The first projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `P`; everywhere else it returns `⊥ = {Γ}`. The neighbourhood relation is
`W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ P ⊆ Z`. -/
def proj0Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hPZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hPZ⟩⟩
      · have hPP : Pp = Pp' := (embPair_injective (hWeq.symm.trans hWeq')).1
        have hPsub : Pp ⊆ Z ∩ Z' := Set.subset_inter hPZ (by rw [hPP]; exact hPZ')
        have hMemP : MemS D Pp := (memS_embPair_inv hD (hWeq ▸ hW)).1
        exact ⟨hW, memS_inter hD hZ hZ' hMemP hPsub, Or.inr ⟨Pp, Qq, hWeq, hPsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hZ'mem) hZZ')
    · subst hWeq
      cases hW'mem with
      | gamma =>
        exact absurd (Set.Subset.antisymm (memS_subset_gamma hW) hW'W)
          (embPair_ne_Gamma D hD Pp Qq)
      | @zero X hX =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        rcases hW'W (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
          ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
      | @pair Pp' Qq' hP' hQ' =>
        obtain ⟨hP'P, -⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hPZ (hP'P hz))⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
