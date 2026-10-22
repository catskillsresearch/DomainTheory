module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_prependN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.consMapN_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.SigTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jU
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.none_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tu_not_mem_jc
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.tc_not_mem_jU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

section SumSig

universe v

variable {β : Type v} {γ : Type v}

omit [DecidableEq A] in

theorem jc_subset_jc {a : A} {X X' : Set β} :
    (jc a X : Set (SigTok A β)) ⊆ jc a X' ↔ X ⊆ X' := by
  constructor
  · intro h t ht; exact tc_mem_jc.mp (h (tc_mem_jc.mpr ht))
  · rintro h w ⟨t, rfl, ht⟩; exact tc_mem_jc.mpr (h ht)

end SumSig

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
