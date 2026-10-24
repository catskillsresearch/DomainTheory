module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.IsComputable
public import DomainTheory.DataTypesAsLattices.Computability.LambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.pack4_proj4
public import DomainTheory.DataTypesAsLattices.Computability.topRecTerm
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Computability.Realizes2
public import DomainTheory.DataTypesAsLattices.Computability.composeC
public import DomainTheory.DataTypesAsLattices.Computability.constComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecComb
public import DomainTheory.DataTypesAsLattices.Computability.addStepC
public import DomainTheory.DataTypesAsLattices.Computability.addC
public import DomainTheory.DataTypesAsLattices.Computability.safePredC
public import DomainTheory.DataTypesAsLattices.Computability.subStepC
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC
public import DomainTheory.DataTypesAsLattices.Computability.leC
public import DomainTheory.DataTypesAsLattices.Computability.pairTerm
public import DomainTheory.DataTypesAsLattices.Computability.arithEnv
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter
public import DomainTheory.DataTypesAsLattices.Computability.sqrtEnv
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepTerm
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtC
public import DomainTheory.DataTypesAsLattices.Computability.unpairEnv
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSquareTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairTestTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpEnv
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpTerm
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC
public import DomainTheory.DataTypesAsLattices.Computability.pairRealizer
public import DomainTheory.DataTypesAsLattices.Computability.precEnv
public import DomainTheory.DataTypesAsLattices.Computability.precTerm
public import DomainTheory.DataTypesAsLattices.Computability.precC
public import DomainTheory.DataTypesAsLattices.Computability.enumFun
public import DomainTheory.DataTypesAsLattices.Computability.enumRangeC
public import DomainTheory.DataTypesAsLattices.Computability.ComputableFin

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eSubset_iff_stage {x : Pomega} {c : Code}
    (hc : Code.eval c = fun k => Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ))
    (n : ℕ) :
    e n ⊆ x ↔ ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true := by
  constructor
  · intro hsub
    let stage : ℕ → ℕ := fun k =>
      if h : n.testBit k = true then
        ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr h), Part.mem_some_iff.mpr rfl⟩)).choose
      else 0
    refine ⟨(Finset.range n).sup stage, fun k hlt => ?_⟩
    by_cases hb : n.testBit k = true
    · refine Or.inr ?_
      have hle : stage k ≤ (Finset.range n).sup stage :=
        Finset.le_sup (Finset.mem_range.mpr hlt)
      have h0 : 0 ∈ evaln (stage k) c k := by
        simp only [stage, hb, ↓reduceDIte]
        exact ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr hb), Part.mem_some_iff.mpr rfl⟩)).choose_spec
      exact (Option.isSome_of_mem (evaln_mono hle h0))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro ⟨s, hs⟩ k hk
    have hlt : k < n := mem_e_lt hk
    have hsome : (evaln s c k).isSome = true :=
      (hs k hlt).resolve_left fun hfalse => Bool.eq_false_iff.mp hfalse (mem_e.mp hk)
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hsome
    have : val ∈ Code.eval c k :=
      evaln_sound (by simpa [Option.mem_def] using hval)
    have : val ∈ (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) := by
      simpa [hc] using this
    exact (Part.mem_assert_iff.mp this).1

end DomainTheory.DataTypesAsLattices
