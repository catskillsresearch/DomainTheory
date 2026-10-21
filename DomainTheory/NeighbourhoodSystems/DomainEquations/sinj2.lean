/-ai
The two-injection into the three-way sum sends an element of the last summand to the sum element whose neighbourhoods are the master together with the two-copies of that element's neighbourhoods.
ai-/
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

/-- The `2`-injection `D₂ ↪ D₀+D₁+D₂`. -/
def sinj2 (x₂ : V₂.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Z, V₂.mem Z ∧ W = j2 Z ∧ x₂.mem Z
  sub := by
    rintro W (rfl | ⟨Z, hZ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) (rfl | ⟨Z', hZ', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Z', hZ', by rw [master3_inter_j2 hZ'], hx'⟩
    · exact Or.inr ⟨Z, hZ, by rw [Set.inter_comm, master3_inter_j2 hZ], hx⟩
    · exact Or.inr ⟨Z ∩ Z', x₂.sub (x₂.inter_mem hx hx'), j2_inter_j2 Z Z', x₂.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr ⟨Z', hZ', rfl, x₂.up_mem hx hZ' (j2_subset_j2.mp hsub)⟩

end SumInj

end DomainTheory.NeighbourhoodSystems
