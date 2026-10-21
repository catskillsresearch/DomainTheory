/-ai
A map f typed in the arrow from a to b lies in the function space from E_a to E_b.

The typing equation writes f as the composite b ∘ f ∘ a. Graph extensionality and the application laws for composites show that f is the graph of its own application. On a pair related by E_a the two arguments are equal and lie in the range of a, so Theorem 4.3 (ii) places the common value of f in the range of b.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem theorem_7_2_ii_of_typed {a b f : Pomega} (hf : typed f (arrowR a b)) :
    (arrowE (Ea a) (Ea b)).mem f := by
  have hf' : f = comp b (comp f a) := by
    simpa [typed, arrowR_app] using hf
  have hgraph : f = graph (fun x => funOf f x) := by
    apply Eq.trans hf'
    apply graph_ext
    intro x
    have : funOf f x = funOf b (funOf f (funOf a x)) := by
      have h1 : funOf f x = funOf (comp b (comp f a)) x :=
        congrArg (fun w => funOf w x) hf'
      rw [h1, comp_app, comp_app]
    rw [comp_app, this]
  refine ⟨hgraph, hgraph, ?_⟩
  intro x y hxy
  rcases hxy with ⟨hx, hy, rfl⟩
  have hfx : typed (funOf f x) b := theorem_4_3_ii hf hx
  exact ⟨hfx, hfx, rfl⟩

end DomainTheory.DataTypesAsLattices
