
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.isBdelta_inter

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem isBdelta_union {U V : Set Pomega} (hU : IsBdelta U) (hV : IsBdelta V) :
    IsBdelta (U ∪ V) := by
  obtain ⟨Bs, hB, rfl⟩ := hU
  obtain ⟨Cs, hC, rfl⟩ := hV
  refine ⟨fun n => Bs (unpair n).1 ∪ Cs (unpair n).2,
    fun n => (hB _).union (hC _), ?_⟩
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    rcases hx with hB' | hC'
    · exact Or.inl (Set.mem_iInter.mp hB' (unpair n).1)
    · exact Or.inr (Set.mem_iInter.mp hC' (unpair n).2)
  · intro hx
    by_cases hB' : x ∈ ⋂ n, Bs n
    · exact Or.inl hB'
    · refine Or.inr (Set.mem_iInter.mpr fun m => ?_)
      have : ¬ ∀ n, x ∈ Bs n := by
        intro hall
        exact hB' (Set.mem_iInter.mpr hall)
      obtain ⟨n, hn⟩ := not_forall.mp this
      have hx' := Set.mem_iInter.mp hx (pair n m)
      simpa [unpair_pair, hn] using hx'

/-
Research remark (Scott 1976, pp. 39–40). Scott asks for LAMBDA-definable
combinators `union` and `inter` that index finite Boolean operations on the
typical `B_δ` set `B` of Table 3:

  `{x | union(f)(g)(x) ∈ B} = {x | f(x) ∈ B} ∪ {x | g(x) ∈ B}`

and likewise for intersection. The combinator API (`S`, `K`, `cond`, `seq2`,
`interC`, …) does not supply these index combinators, and Scott himself
leaves their extraction as an investigation. Set-theoretic continuous
indexers exist (`typicalBdelta_universal`, `isBdelta_union`,
`isBdelta_inter`), but LAMBDA-definability is not recorded as a theorem.
-/

end DomainTheory.DataTypesAsLattices
