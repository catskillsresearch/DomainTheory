/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_false
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_prodTokNbhd_true
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTokNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_mem_prodTokNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_fstTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.mem_sndTok

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- Scott's (3) for the product: membership of `X ∪ Y` splits into its two slices. -/
theorem prodTok_mem_split {z : (prodTok D₀ D₁).Element} {X Y : Set Str}
    (hX : D₀.mem X) (hY : D₁.mem Y) :
    z.mem (prodTokNbhd X Y) ↔
      z.mem (prodTokNbhd X D₁.master) ∧ z.mem (prodTokNbhd D₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prodTok_mem_prodTokNbhd hX D₁.master_mem) ?_,
            z.up_mem h (prodTok_mem_prodTokNbhd D₀.master_mem hY) ?_⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨subset_rfl, D₁.sub_master hY⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodTokNbhd_inter, Set.inter_eq_left.mpr (D₀.sub_master hX),
      Set.inter_eq_right.mpr (D₁.sub_master hY)] at this

end Exercise619

end DomainTheory.NeighbourhoodSystems
