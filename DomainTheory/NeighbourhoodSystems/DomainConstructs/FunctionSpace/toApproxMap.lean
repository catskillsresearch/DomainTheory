module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The relation `X φ̂ Y ↔ [X, Y] ∈ φ` of a filter `φ`.
Intersectivity is the payoff of positivity (`[X,Y]∩[X,Y'] = [X,Y∩Y']` is non-empty, so `Y∩Y' ∈ 𝒟₁`). -/
def toApproxMap (φ : (funSpace V₀ V₁).Element) : ApproximableMap V₀ V₁ where
  rel X Y := φ.mem (step X Y)
  rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_dom hf
  rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_cod hf
  master_rel := by show φ.mem (step V₀.master V₁.master); rw [step_master_eq]; exact φ.master_mem
  inter_right := by
    intro X Y Y' h h'
    obtain ⟨f, hf⟩ := (φ.sub h).2
    obtain ⟨f', hf'⟩ := (φ.sub h').2
    have hY : V₁.mem Y := f.rel_cod hf
    have hY' : V₁.mem Y' := f'.rel_cod hf'
    show φ.mem (step X (Y ∩ Y'))
    rw [← step_inter_right hY hY']
    exact φ.inter_mem h h'
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY'
    show φ.mem (step X' Y')
    exact φ.up_mem h (step_mem hX' hY') (step_subset hX' hY' hX'X hYY')

end DomainTheory.NeighbourhoodSystems
