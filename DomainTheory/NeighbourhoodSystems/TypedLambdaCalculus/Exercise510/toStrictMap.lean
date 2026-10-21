/-ai
The strict map represented by a filter of the strict function space relates two sets when their step set belongs to the filter. The domain and codomain are those of a witness in the step. The step of the two masters is the universe, which belongs to the filter. Intersection on the right rewrites the step of an intersection of outputs as the intersection of the two steps, using the codomains of two witnesses. Monotonicity produces a witness relation on the smaller domain and larger codomain and pushes the original step up to the new step. Strictness is the strictness of a witness in the step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_inter_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_subset
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_mem_of_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **The strict map represented by a filter.** `X (toStrictMap φ) Y ↔ [X, Y] ∈ φ`. It is *strict*
because the step `[Δ₀, Y]` with `Y ≠ Δ₁` is empty (no strict map relates `Δ₀` to a proper output),
hence not a neighbourhood, so it cannot belong to `φ`. -/
def toStrictMap (φ : (strictFun V₀ V₁).Element) : StrictMap V₀ V₁ :=
  ⟨{ rel := fun X Y => φ.mem (sstep X Y)
     rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_dom hf
     rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_cod hf
     master_rel := by
       show φ.mem (sstep V₀.master V₁.master); rw [sstep_master_eq]; exact φ.master_mem
     inter_right := by
       intro X Y Y' h h'
       obtain ⟨f, hf⟩ := (φ.sub h).2
       obtain ⟨f', hf'⟩ := (φ.sub h').2
       have hY : V₁.mem Y := f.1.rel_cod hf
       have hY' : V₁.mem Y' := f'.1.rel_cod hf'
       show φ.mem (sstep X (Y ∩ Y'))
       rw [← sstep_inter_right hY hY']
       exact φ.inter_mem h h'
     mono := by
       intro X X' Y Y' h hX'X hYY' hX' hY'
       obtain ⟨g, hg⟩ := (φ.sub h).2
       have hg' : g.1.rel X' Y' := g.1.mono hg hX'X hYY' hX' hY'
       show φ.mem (sstep X' Y')
       exact φ.up_mem h (sstep_mem_of_mem (g := g) hg') (sstep_subset hX' hY' hX'X hYY') },
   by
     intro Y h
     obtain ⟨g, hg⟩ := (φ.sub h).2
     exact g.2 hg⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
