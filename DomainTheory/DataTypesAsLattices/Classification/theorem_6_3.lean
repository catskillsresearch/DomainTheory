/-ai
Scott's 𝔊δ theorem (1976, Theorem 6.3) states that a set U is a Scott Gδ set if and only if U is the set of x at which some Scott-continuous f takes the value ⊤.

If U is the intersection of Scott-open sets, the pair-indexed packing of their top characteristics is Scott continuous, and that packing equals ⊤ at x exactly when every top characteristic equals ⊤ at x, which is membership in every set of the intersection. Conversely, if U is the set of x with f(x) equal to ⊤, then U is the intersection of the Scott-open sets of x with n in f(x), and x lies in all of them exactly when f(x) is ⊤.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.pairIndexed_eq_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace
























/-- **Scott 1976, Theorem 6.3 (The 𝔊_δ theorem).** -/
theorem theorem_6_3 :
    ∀ U, IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = topElem} := by
  intro U
  constructor
  · rintro ⟨Us, hUs, rfl⟩
    let fs := fun n => charTop (Us n)
    refine ⟨pairIndexed fs, pairIndexed_isScottContinuous fs fun n =>
      charTop_isScottContinuous (Us n), ?_⟩
    ext x
    constructor
    · intro hx
      change pairIndexed fs x = topElem
      exact (pairIndexed_eq_top fs x).mpr fun n =>
        (charTop_eq_top (hUs n) x).mpr (Set.mem_iInter.mp hx n)
    · intro hf
      have hf' : pairIndexed fs x = topElem := hf
      exact Set.mem_iInter.mpr fun n =>
        (charTop_eq_top (hUs n) x).mp ((pairIndexed_eq_top fs x).mp hf' n)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun n => {x | n ∈ f x}, fun n => mem_preimage_isScottOpen hf n, ?_⟩
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      have : f x = topElem := hx
      simp [this]
    · intro hx
      ext k
      constructor
      · intro _; trivial
      · intro _
        exact Set.mem_iInter.mp hx k

end DomainTheory.DataTypesAsLattices
