module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN_singleton

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

theorem memCn_prependN (σ : Strn A) {X : Set (Strn A)} (hX : memCn X) : memCn (prependN σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prependN_coneN σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prependN_singleton σ ρ⟩

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
