module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.algHom_fix

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


/-- **`descAlgHom` is the least homomorphism**: `val ≤ g` for every homomorphism `g : Exp → D`. The
Kleene iterates `valₙ` lie below any fixed point `g` (induction: `val₀ = ⊥ ≤ g`, and the operator is
monotone with `g` its own fixed point), so their union `val` does too. This is the easy half of
initiality; the matching `g ≤ val` (so `g = val`) is the projection-chain argument of Phase 4. -/
theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

end Existence
end Exercise619
end DomainTheory.NeighbourhoodSystems
