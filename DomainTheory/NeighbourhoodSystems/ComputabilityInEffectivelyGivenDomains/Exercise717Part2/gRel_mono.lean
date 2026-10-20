/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_cod
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Monotonicity (Scott's 2.1(iii)). -/
theorem gRel_mono (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {W' Z'}, W' ⊆ W → Z ⊆ Z' → MemS D W' → E.mem Z' → GRel u v W' Z' := by
  induction h with
  | @gamma Z hZ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      subst hZ
      have hZ' : Z' = E.master := Set.Subset.antisymm (E.sub_master hZ'mem) hZZ'
      subst hZ'
      exact gRel_master hW'mem
  | @leaf X Z hrel =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨X', hX'mem, rfl⟩ := memS_sub_embZero hD hW'mem hW'W
      exact GRel.leaf (u.mono hrel (embZero_subset.mp hW'W) hZZ' hX'mem hZ'mem)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨P', Q', hP'mem, hQ'mem, rfl⟩ := memS_sub_embPair hD hW'mem hW'W
      obtain ⟨hP'P, hQ'Q⟩ := embPair_subset.mp hW'W
      refine GRel.node (ihP hP'P subset_rfl hP'mem (gRel_cod hP))
        (ihQ hQ'Q subset_rfl hQ'mem (gRel_cod hQ)) ?_
      exact v.mono hvrel subset_rfl hZZ'
        (prod_mem_prodNbhd (gRel_cod hP) (gRel_cod hQ)) hZ'mem

end Exercise717

end DomainTheory.NeighbourhoodSystems
