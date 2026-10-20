module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- Scott's injection `x^§ = {Γ} ∪ {0X ∣ X ∈ x}` of a `D`-element into `D^§`. -/
def inSharp (x : D.Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ X, x.mem X ∧ W = embZero X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact MemS.gamma
    · exact MemS.zero (x.sub hX)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma (x.sub hX'))]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma (x.sub hX))]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embZero_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' => exact Or.inr ⟨X', x.up_mem hX hX' (embZero_subset.mp hsub), rfl⟩
      | @pair P Q hP hQ =>
        exfalso
        obtain ⟨a, ha⟩ := hD X (x.sub hX)
        have hmem : (([], a) : List Bool × α) ∈ embPair P Q := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
