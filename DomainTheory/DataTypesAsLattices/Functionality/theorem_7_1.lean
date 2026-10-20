module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices










/-- **Scott 1976, Theorem 7.1 (The closure theorem).** -/
theorem theorem_7_1 (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f ↔
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ {f x}, (arrowE A B).mem f → A.mem x → B.mem (funOf f x)) ∧
      (∀ u, (prodE A B).mem u ↔
        u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u ↔
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    constructor
    · intro hf
      exact ⟨hf.1, fun x y hxy => hf.2.2 x y hxy⟩
    · intro ⟨hf, hpres⟩
      exact ⟨hf, hf, hpres⟩
  · intro f x hf hx
    exact hf.2.2 x x hx
  · intro u
    constructor
    · intro hu
      exact ⟨hu.1, hu.2.2.1, hu.2.2.2⟩
    · intro ⟨hu, hA, hB⟩
      exact ⟨hu, hu, hA, hB⟩
  · intro u
    constructor
    · intro hu
      rcases hu with ⟨hu, _, hA⟩ | ⟨hu, _, hB⟩
      · exact Or.inl ⟨hu, hA⟩
      · exact Or.inr ⟨hu, hB⟩
    · intro h
      rcases h with ⟨hu, hA⟩ | ⟨hu, hB⟩
      · exact Or.inl ⟨hu, hu, hA⟩
      · exact Or.inr ⟨hu, hu, hB⟩

end DomainTheory.DataTypesAsLattices
