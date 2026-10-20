/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Continuous
import DomainTheory.DataTypesAsLattices.Graph.Basic
import DomainTheory.DataTypesAsLattices.Graph.mem_graph
import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_ii


namespace DomainTheory.DataTypesAsLattices





theorem theorem_1_2_iii (u : Pomega) :
    graph (funOf u) = u ↔ IsGraph u := by
  constructor
  · intro heqGraph k m n hkm hkn
    have hmem : pair k m ∈ graph (funOf u) := heqGraph.symm ▸ hkm
    rcases mem_graph.mp hmem with ⟨k', m', hp, hmfun⟩
    have hk : k = k' := (pair_inj hp).1
    have hm : m = m' := (pair_inj hp).2
    have hmfun' : m ∈ funOf u (e k) := by
      rw [hk, hm]; exact hmfun
    rcases hmfun' with ⟨j, hj, hpj⟩
    have hgraph : pair n m ∈ graph (funOf u) :=
      mem_graph.mpr ⟨n, m, rfl, ⟨j, subset_trans hj hkn, hpj⟩⟩
    exact heqGraph ▸ hgraph
  · intro hu
    apply subset_antisymm
    · intro p hp
      rcases hp with ⟨n, m, rfl, ⟨k, hk, hkm⟩⟩
      exact hu hkm hk
    · exact theorem_1_2_ii u

end DomainTheory.DataTypesAsLattices
