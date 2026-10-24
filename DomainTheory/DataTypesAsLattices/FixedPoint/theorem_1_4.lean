module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.chain_lemma
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot_mono

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 1.4 (The fixed-point theorem).** -/
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  constructor
  · -- f(fix f) = ⋃ f(fⁿ(∅)) = ⋃ fⁿ⁺¹(∅) = fix f
    have hchain := chain_lemma hf (iterateBot f) (iterateBot_mono hf)
    unfold fix
    rw [hchain]
    ext k
    constructor
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      cases n with
      | zero => simp [iterateBot, botElem] at hkn
      | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩
  · intro x hx k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have hsub : ∀ n, iterateBot f n ⊆ x := by
      intro n
      induction n with
      | zero => simp [iterateBot, botElem]
      | succ n ih =>
        simpa [iterateBot, hx] using isScottContinuous_monotone hf ih
    exact hsub n hkn

end DomainTheory.DataTypesAsLattices
