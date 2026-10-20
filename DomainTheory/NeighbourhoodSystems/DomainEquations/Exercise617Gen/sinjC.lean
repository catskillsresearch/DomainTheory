module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_inter_jc_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc_subset_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_mem_masterSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.masterSig_inter_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.eq_masterSig_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.sumSig_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

variable (V : NeighborhoodSystem β)

variable {V}

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- The `a`-th copy injection `V ↪ 𝟙+Σ_a V`: send `x∈|V|` to the sum element whose proper
neighbourhoods are the `a`-copies `aX` with `X∈x`. -/
def sinjC (a : A) (x : V.Element) : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ ∃ X, V.mem X ∧ W = jc a X ∧ x.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [masterSig_inter_jc hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x.sub (x.inter_mem hx hx'), jc_inter_jc_same a X X', x.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective heq
        exact Or.inr ⟨X', hX', rfl, x.up_mem hx hX' (jc_subset_jc.mp hsub)⟩

end SumSig

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
