/-ai
The one-point generator on the fixed-point token set is a subsystem of its image under a rooted grammar expression. This is the base of the tower.

The master of the image equals the token image of the fixed-point set, which equals the fixed-point set, so the masters agree. A neighbourhood of the generator is that master, hence a neighbourhood of the image, and the intersection of two such neighbourhoods is the fixed-point set again.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix_fixed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_continuous
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2emap_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2enaryOp_rootedConst
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_continuous
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_continuous_mp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2eobj_subsystem
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **`{Γ} ◁ T({Γ})`** — Scott's hypothesis for Theorem 6.14, the base of the tower. (This is the
content of `gExists_singleton_subsystem`, here at the *explicit* generator `Γ = gFix T`.) -/
theorem gBase (T : GExpr) (hT : T.RootedConst) : (gGen T).sys ◁ (T.obj (gGen T)).sys := by
  have hmaster : (T.obj (gGen T)).sys.master = gFix T :=
    (gFun_eq_master T (gFix_nonempty T)).symm.trans (gFix_fixed T hT)
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have heq : X = (T.obj (gGen T)).sys.master := (hX : X = gFix T).trans hmaster.symm
    rw [heq]; exact (T.obj (gGen T)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = gFix T
    rw [show X = gFix T from hX, show Y = gFix T from hY, Set.inter_self]

end Exercise619

end DomainTheory.NeighbourhoodSystems
