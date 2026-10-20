/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem85.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}






section HardDirection

variable {a : ApproximableMap E E}



variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)




/-- **`e` distributes over directed sups of `a`-fixed families.** `Fix(a)` is not itself a
`NeighborhoodSystem.Element` type, so this is proved directly by antisymmetry (rather than via a
generic "order isos preserve directed sups" lemma): both inequalities reduce to `le_iSupDirected`/
`iSupDirected_le` on the `E`- and `F`-sides plus monotonicity of `e`/`e.symm`. -/
theorem e_apply_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i)
    (hSfix : a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir)
    (hdir' : ∀ i j : I, ∃ k, e ⟨d i, hfix i⟩ ≤ e ⟨d k, hfix k⟩ ∧
      e ⟨d j, hfix j⟩ ≤ e ⟨d k, hfix k⟩) :
    e ⟨iSupDirected d hdir, hSfix⟩ = iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' := by
  apply le_antisymm
  · have hstep : (⟨iSupDirected d hdir, hSfix⟩ : FixSet a) ≤
        e.symm (iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir') := by
      show iSupDirected d hdir ≤ _
      apply iSupDirected_le
      intro i
      show d i ≤ _
      have hle : e ⟨d i, hfix i⟩ ≤ iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' :=
        le_iSupDirected (fun i => e ⟨d i, hfix i⟩) hdir' i
      have := e.symm.monotone hle
      rwa [e.symm_apply_apply] at this
    have := e.monotone hstep
    rwa [e.apply_symm_apply] at this
  · apply iSupDirected_le
    intro i
    exact e.monotone (le_iSupDirected d hdir i)

end HardDirection
end DomainTheory.Neighborhood
