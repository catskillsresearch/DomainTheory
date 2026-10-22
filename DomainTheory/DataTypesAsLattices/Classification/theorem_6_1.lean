/-ai
Scott's 𝔊 theorem (1976, Theorem 6.1) states that for every Scott-continuous f the set of x with 0 in f(x) is Scott open, and that every Scott-open set has this form for some Scott-continuous f.

If f is Scott continuous, that set is the Scott-open set whose basis consists of the finite sets en with 0 in f(en). Membership of 0 in f(x) is membership in the Scott union of f along x, so some en contained in x already has 0 in f(en), and the converse is monotonicity of f. Conversely, the open characteristic of a Scott-open set U is Scott continuous. If x lies in U, some basis element en contained in x lies in U and witnesses that 0 lies in the characteristic at x. If 0 lies in the characteristic at x, some en contained in x lies in U, and U is an upper set, so x lies in U.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- **Scott 1976, Theorem 6.1 (The 𝔊 theorem).** -/
theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  constructor
  · intro f hf
    refine ⟨{n | 0 ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : 0 ∈ scottUnion f x := by rwa [← hf.out x]
      obtain ⟨n, hn, h0⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, h0, hn⟩
    · intro hx
      obtain ⟨n, h0, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn h0
  · intro U hU
    refine ⟨charOpen U, charOpen_isScottContinuous U, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨B, rfl⟩ := hU
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨rfl, n, hxn, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
    · intro ⟨_, n, hn, hne⟩
      exact isScottOpen_isUpper hU hne hn

end DomainTheory.DataTypesAsLattices
