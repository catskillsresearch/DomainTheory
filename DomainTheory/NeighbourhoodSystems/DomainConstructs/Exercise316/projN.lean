/-ai
The n-th coordinate projection from the infinite iterate to the original domain relates W to X when W is an iterate neighbourhood, X is a neighbourhood, and the n-th fiber of W is contained in X. The domain and codomain laws are those two memberships. The master is related because the n-th fiber of the iterate master is the original master. Intersecting two related neighbourhoods intersects the targets and the fiber inclusions. A larger domain neighbourhood and a larger target remain related by monotonicity of fibers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_component

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (V : NeighborhoodSystem α)

variable {V}

open ApproximableMap

/-- The `n`-th coordinate projection `projN n : 𝒟^∞ → 𝒟`, `W (projN n) X ↔ fiber W n ⊆ X`. -/
def projN (V : NeighborhoodSystem α) (n : ℕ) : ApproximableMap (iterSys V) V where
  rel W X := (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, V.master_mem, by rw [fiber_iterSys_master]⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V.inter_mem hX hX' (hW.1 n) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, _, hsub⟩ hW₂W hXX₂ hW₂ hX₂
    exact ⟨hW₂, hX₂, (fiber_mono hW₂W n).trans (hsub.trans hXX₂)⟩

end DomainTheory.NeighbourhoodSystems
