/-ai
If X' is a neighbourhood of the first system, Y' is a neighbourhood of the second, X' is contained in X, and Y is contained in Y', then the step neighbourhood of X and Y is contained in the step neighbourhood of X' and Y'.

A map in the first step lies in the second by monotonicity of that map, using the two inclusions and the neighbourhood hypotheses on X' and Y'.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `X' ⊆ X` and `Y ⊆ Y'` imply `[X, Y] ⊆ [X', Y']`. -/
theorem step_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (step X Y : Set (ApproximableMap V₀ V₁)) ⊆ step X' Y' := by
  intro f hf
  exact f.mono hf hX'X hYY' hX' hY'

end DomainTheory.NeighbourhoodSystems
