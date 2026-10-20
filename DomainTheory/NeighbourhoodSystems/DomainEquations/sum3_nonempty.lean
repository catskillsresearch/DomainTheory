module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

open Example62C in
/-- Every neighbourhood of the three-way separated sum `sum3` is non-empty (so `sum3` is again an
object of the `∅`-free category). -/
theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)

end DomainTheory.NeighbourhoodSystems
