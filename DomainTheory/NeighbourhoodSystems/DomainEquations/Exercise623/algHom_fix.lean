/-ai
Every homomorphism g from Exp to an algebra is a fixed point of the operator sending h to the structure map composed with T(h) composed with the inverse structure map. This is the homomorphism square, rearranged by the identity that the structure map composed with its inverse is the identity on Exp.

Rewrite g as g composed with the identity on Exp, replace that identity by the structure map composed with its inverse, reassociate, substitute the homomorphism square, and reassociate once more.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expHom_comp_expInv

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))


/-- **Every homomorphism `g : Exp → D` is a fixed point** of the operator `λh. k ∘ T(h) ∘ j`. This is
the homomorphism square `g ∘ i = k ∘ T(g)` (`g.comm`) rearranged by `i ∘ j = I`. -/
theorem algHom_fix (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1 = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1
      = (g.hom.1).comp (idMap (Exp N hN).sys) := (comp_idMap _).symm
    _ = (g.hom.1).comp ((expHom N hN).comp (expInv N hN)) := by rw [expHom_comp_expInv]
    _ = ((g.hom.1).comp (expHom N hN)).comp (expInv N hN) := (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp (expInv N hN) :=
          congrArg (fun m => m.comp (expInv N hN)) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := comp_assoc _ _ _

end Existence
end Exercise619
end DomainTheory.NeighbourhoodSystems
