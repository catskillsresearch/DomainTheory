module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- Scott's pairing `⟨x, y⟩ = {Γ} ∪ {1P ∪ 2Q ∣ P ∈ x, Q ∈ y}` of two `D^§`-elements. -/
def pairSharp (x y : (Dsharp D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ P Q, x.mem P ∧ y.mem Q ∧ W = embPair P Q
  sub := by
    rintro W (rfl | ⟨P, Q, hP, hQ, rfl⟩)
    · exact MemS.gamma
    · exact MemS.pair (x.sub hP) (y.sub hQ)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) (rfl | ⟨P', Q', hP', hQ', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨P', Q', hP', hQ', by
        rw [Set.inter_eq_right.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP'))
          (memS_subset_gamma (y.sub hQ')))]⟩
    · exact Or.inr ⟨P, Q, hP, hQ, by
        rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP))
          (memS_subset_gamma (y.sub hQ)))]⟩
    · exact Or.inr ⟨P ∩ P', Q ∩ Q', x.inter_mem hP hP', y.inter_mem hQ hQ', by rw [embPair_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD (x.sub hP)) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        exact hcons (hsub ht).1
      | @pair P' Q' hP' hQ' =>
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact Or.inr ⟨P', Q', x.up_mem hP hP' hPP, y.up_mem hQ hQ' hQQ, rfl⟩

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
