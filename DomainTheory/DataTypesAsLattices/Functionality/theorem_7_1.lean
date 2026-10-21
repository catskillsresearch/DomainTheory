/-ai
Scott 1976, Theorem 7.1, the closure theorem. Membership in the function space from A to B is being a graph of one's own application and preserving relatedness. Such a map sends an element of A to an element of B. Membership in the product is being the pair of one's own components, with those components in A and in B. Membership in the sum is being a left injection of an element of A or a right injection of an element of B.

Each equivalence is unpacked from the definitions. A function-space element gives the graph equation and the preservation clause, and the converse repeats the graph equation. Preservation on a pair related to itself gives the action on elements. A product element is the pair of its components, and the converse repeats the pair equation. A sum element keeps one tag and its component relation, and the converse repeats the injection equation.
ai-/

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
