/-ai
Scott 1976, Theorem 7.2 (ii). For retracts a and b, a map typed in the arrow from a to b lies in the function space from E_a to E_b. Relatedness in that function space passes to the two maps retracted by the arrow, as relatedness in E of the arrow. Relatedness in E of the arrow returns relatedness in the function space.

The first conjunct is the lemma for a typed map. For the second, the arrow retract places both retracted maps in the range of the arrow. Comparing their graphs, preservation at the value a(x), which lies in the range of a, gives equal applications, and those values lie in the range of b, so the composites agree. For the third, relatedness in E of the arrow forces the two elements to be equal, and the typed-map lemma supplies the function-space relation of that map with itself.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_2_ii_of_typed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.2 (ii).** Maps in `E_{a ∘→ b}` are graphs of
maps from `a` to `b`, corresponding to `E_a → E_b`. -/
theorem theorem_7_2_ii {a b : Pomega} (ha : Retract a) (hb : Retract b)
    (f g : Pomega) :
    (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
      ((arrowE (Ea a) (Ea b)).rel f g →
        (Ea (arrowR a b)).rel (funOf (arrowR a b) f) (funOf (arrowR a b) g)) ∧
      ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g) := by
  refine ⟨fun hf => theorem_7_2_ii_of_typed hf, ?_, ?_⟩
  · intro hfg
    rcases hfg with ⟨hfgraph, hggraph, hpres⟩
    have hftyped : typed (funOf (arrowR a b) f) (arrowR a b) :=
      (retract_app (arrowR_isRetract ha hb) f).symm
    have hgtyped : typed (funOf (arrowR a b) g) (arrowR a b) :=
      (retract_app (arrowR_isRetract ha hb) g).symm
    refine ⟨hftyped, hgtyped, ?_⟩
    rw [arrowR_app, arrowR_app]
    apply graph_ext
    intro x
    simp only [comp_app]
    have hax : typed (funOf a x) a := (retract_app ha x).symm
    have hsame := hpres (funOf a x) (funOf a x) ⟨hax, hax, rfl⟩
    have hfeq : funOf f (funOf a x) = funOf g (funOf a x) := hsame.2.2
    have hfb : typed (funOf f (funOf a x)) b := hsame.1
    have hgb : typed (funOf g (funOf a x)) b := hsame.2.1
    rw [← hfb, ← hgb, hfeq]
  · intro hfg
    rcases hfg with ⟨hf, hg, rfl⟩
    have hmem := theorem_7_2_ii_of_typed hf
    exact ⟨hmem.1, hmem.1, hmem.2.2⟩

end DomainTheory.DataTypesAsLattices
