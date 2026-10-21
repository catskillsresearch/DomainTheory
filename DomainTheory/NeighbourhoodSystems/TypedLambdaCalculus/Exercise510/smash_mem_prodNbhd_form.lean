/-ai
Every neighbourhood of the smash product is a product of a neighbourhood of the first system and a neighbourhood of the second.

The master case is the product of the two masters, and a proper smash neighbourhood is already a product of its two factors.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- Every smash neighbourhood is a product neighbourhood `A ∪ B` (the master is `Δ₀ ∪ Δ₁`). -/
theorem smash_mem_prodNbhd_form {W : Set (α ⊕ β)} (hW : (smash V₀ V₁).mem W) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ W = prodNbhd A B := by
  rcases hW with rfl | ⟨X, Y, hX, _, hY, _, rfl⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, rfl⟩
  · exact ⟨X, Y, hX, hY, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
