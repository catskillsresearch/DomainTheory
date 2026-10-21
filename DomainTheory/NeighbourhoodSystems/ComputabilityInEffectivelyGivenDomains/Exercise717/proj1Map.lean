/-ai
The second projection of the pair part of the sharp domain relates neighbourhoods W and Z of that domain when Z is the master neighbourhood, or W is a paired embedding whose right-hand neighbourhood is contained in Z. The domain and codomain are those memberships, and the master neighbourhood is related to itself. If either target in an intersection is the master, the intersection keeps the other target; if both come from the same paired embedding, injectivity matches the right-hand children and their inclusions meet. A smaller source in the master case must itself be the master, and a smaller source in the paired case cannot be the master or a zero embedding, so it is a paired embedding whose right-hand child is carried into the larger target.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **The second projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `Q`; everywhere else it returns `⊥ = {Γ}`. The exact mirror of `proj0Map`
with the *second* component: `W proj₁ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ Q ⊆ Z`. -/
def proj1Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Qq ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hQZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hQZ⟩⟩
      · have hQQ : Qq = Qq' := (embPair_injective (hWeq.symm.trans hWeq')).2
        have hQsub : Qq ⊆ Z ∩ Z' := Set.subset_inter hQZ (by rw [hQQ]; exact hQZ')
        have hMemQ : MemS D Qq := (memS_embPair_inv hD (hWeq ▸ hW)).2
        exact ⟨hW, memS_inter hD hZ hZ' hMemQ hQsub, Or.inr ⟨Pp, Qq, hWeq, hQsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hQZ⟩
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
        obtain ⟨-, hQ'Q⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hQZ (hQ'Q hz))⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
