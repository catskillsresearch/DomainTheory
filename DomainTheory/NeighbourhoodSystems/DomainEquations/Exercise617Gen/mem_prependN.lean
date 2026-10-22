module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.prependN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in

@[simp] theorem mem_prependN {σ : Strn A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ prependN σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
