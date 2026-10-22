module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `0`-injection `D₀ ↪ D₀+D₁+D₂`: send `x₀∈|D₀|` to the sum element whose only proper
neighbourhoods are the `0`-copies `0X` with `X∈x₀`. -/
def sinj0 (x₀ : V₀.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ X, V₀.mem X ∧ W = j0 X ∧ x₀.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [master3_inter_j0 hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, master3_inter_j0 hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x₀.sub (x₀.inter_mem hx hx'), j0_inter_j0 X X', x₀.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', hX', rfl, x₀.up_mem hx hX' (j0_subset_j0.mp hsub)⟩
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2

end SumInj

end DomainTheory.NeighbourhoodSystems
