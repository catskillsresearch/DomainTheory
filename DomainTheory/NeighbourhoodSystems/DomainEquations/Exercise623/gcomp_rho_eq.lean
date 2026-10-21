/-ai
Every homomorphism g from Exp agrees with the canonical Kleene iterate after the n-th projection: g composed with that projection equals the n-th iterate. The sequence is forced by the recursion and does not depend on the choice of g.

The zero case is the base identity. At a successor, the recursion for the composite with the next projection, the inductive hypothesis, and the successor clause of the iterates give the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- **`g ∘ ρₙ = val₀ₙ`**: every homomorphism `g` agrees with the canonical Kleene iterate after the
`n`-th projection — the sequence is forced by the recursion, independent of `g`. -/
theorem gcomp_rho_eq (g : AlgHom (ExpAlg N hN) B) :
    ∀ n, g.hom.1.comp (rho hN n) = descRel hN B n
  | 0 => gcomp_rho_zero hN B g
  | n + 1 => by rw [gcomp_rho_succ hN B g n, gcomp_rho_eq g n, ← descRel_succ]

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
