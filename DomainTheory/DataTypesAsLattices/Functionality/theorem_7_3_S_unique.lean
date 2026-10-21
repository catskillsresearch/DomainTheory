/-ai
A combinator s that is extensional in its first argument, whose application is extensional in the second argument, and that lies in every function space (A → (B → C)) → ((A → B) → (A → C)), equals the combinator S.

The empty equivalences give the graph equation for s. Extensionality replaces the first argument f by the graph of its double application and the second argument g by the graph of its application. The closure theorem at the empty equivalences, whose relation is empty, shows that the retracted values are graphs. At a third argument, the singleton equivalences of that argument, of g applied there, and of f applied to both, together with the closure theorem, force the triple application to equal the corresponding value of f and g, which is the triple application law for S.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE_mem
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app3
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app2_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.eta2_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem theorem_7_3_S_unique (s : Pomega)
    (hη1 : ∀ f, funOf s f =
      funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y))))
    (hη2 : ∀ f g, funOf (funOf s f) g =
      funOf (funOf s f) (graph (fun x => funOf g x)))
    (hs : ∀ A B C,
      (arrowE (arrowE A (arrowE B C))
        (arrowE (arrowE A B) (arrowE A C))).mem s) :
    s = Scomb := by
  have hsgraph : s = graph (fun f => funOf s f) := (hs emptyE emptyE emptyE).1
  apply graph_funOf_ext hsgraph Scomb_isGraph
  intro f
  let f' : Pomega := graph (fun x => graph (fun y => funOf (funOf f x) y))
  have hf'app (z : Pomega) : funOf f' z = graph (fun y => funOf (funOf f z) y) :=
    eta2_app f z
  have hf'graph : f' = graph (fun z => funOf f' z) := by
    apply graph_ext
    intro z
    exact (hf'app z).symm
  have hsf : funOf s f = funOf s f' := hη1 f
  have hsf'graph : funOf s f' = graph (fun g => funOf (funOf s f') g) := by
    have hf'mem : (arrowE emptyE (arrowE emptyE emptyE)).mem f' :=
      ⟨hf'graph, hf'graph, fun _ _ h => False.elim h⟩
    have := (theorem_7_1 (arrowE emptyE (arrowE emptyE emptyE))
      (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE))).2.1
      (hs emptyE emptyE emptyE) hf'mem
    exact this.1
  apply graph_funOf_ext (by rw [hsf]; exact hsf'graph) (Scomb_app_isGraph f)
  intro g
  let g' : Pomega := graph (funOf g)
  have hg'app (z : Pomega) : funOf g' z = funOf g z :=
    beta (funOf_isScottContinuous g) z
  have hg'graph : g' = graph (fun z => funOf g' z) := by
    apply graph_ext
    intro z
    exact (hg'app z).symm
  have hsg : funOf (funOf s f) g = funOf (funOf s f) g' := hη2 f g
  have hsg' : funOf (funOf s f) g' = funOf (funOf s f') g' := by
    rw [hsf]
  have hsg'graph :
      funOf (funOf s f') g' =
        graph (fun z => funOf (funOf (funOf s f') g') z) := by
    have hg'mem : (arrowE emptyE emptyE).mem g' :=
      ⟨hg'graph, hg'graph, fun _ _ h => False.elim h⟩
    have hf'mem : (arrowE emptyE (arrowE emptyE emptyE)).mem f' :=
      ⟨hf'graph, hf'graph, fun _ _ h => False.elim h⟩
    have hsf'mem :
        (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE)).mem (funOf s f') :=
      (theorem_7_1 (arrowE emptyE (arrowE emptyE emptyE))
        (arrowE (arrowE emptyE emptyE) (arrowE emptyE emptyE))).2.1
        (hs emptyE emptyE emptyE) hf'mem
    exact ((theorem_7_1 (arrowE emptyE emptyE)
      (arrowE emptyE emptyE)).2.1 hsf'mem hg'mem).1
  apply graph_funOf_ext
    (by rw [hsg, hsg']; exact hsg'graph) (Scomb_app2_isGraph f g)
  intro arg
  let A := singletonE arg
  let B := singletonE (funOf g arg)
  let C := singletonE (funOf (funOf f arg) (funOf g arg))
  have hf'memABC : (arrowE A (arrowE B C)).mem f' := by
    refine ⟨hf'graph, hf'graph, ?_⟩
    intro x₁ x₂ hx₁₂
    have hx₁ : x₁ = arg := hx₁₂.1
    have hx₂ : x₂ = arg := hx₁₂.2
    have hfxgraph (z : Pomega) :
        funOf f' z = graph (fun y => funOf (funOf f' z) y) := by
      rw [hf'app]
      apply graph_ext
      intro y
      exact (beta (funOf_isScottContinuous (funOf f z)) y).symm
    rw [hx₁, hx₂]
    refine ⟨hfxgraph arg, hfxgraph arg, ?_⟩
    intro y₁ y₂ hy
    have hy₁ : y₁ = funOf g arg := hy.1
    have hy₂ : y₂ = funOf g arg := hy.2
    rw [hy₁, hy₂, hf'app]
    have happ :
        funOf (graph (fun y => funOf (funOf f arg) y)) (funOf g arg) =
          funOf (funOf f arg) (funOf g arg) :=
      beta (funOf_isScottContinuous (funOf f arg)) (funOf g arg)
    exact happ.symm ▸ ⟨rfl, rfl⟩
  have hg'memAB : (arrowE A B).mem g' := by
    refine ⟨hg'graph, hg'graph, ?_⟩
    intro x₁ x₂ hx₁₂
    have hx₁ : x₁ = arg := hx₁₂.1
    have hx₂ : x₂ = arg := hx₁₂.2
    rw [hx₁, hx₂, hg'app]
    exact ⟨rfl, rfl⟩
  have hsf'mem :
      (arrowE (arrowE A B) (arrowE A C)).mem (funOf s f') :=
    (theorem_7_1 (arrowE A (arrowE B C))
      (arrowE (arrowE A B) (arrowE A C))).2.1 (hs A B C) hf'memABC
  have hsg'mem : (arrowE A C).mem (funOf (funOf s f') g') :=
    (theorem_7_1 (arrowE A B) (arrowE A C)).2.1 hsf'mem hg'memAB
  have hxA : A.mem arg := (singletonE_mem arg arg).mpr rfl
  have hval : C.mem (funOf (funOf (funOf s f') g') arg) :=
    (theorem_7_1 A C).2.1 hsg'mem hxA
  have hval' : funOf (funOf (funOf s f') g') arg =
      funOf (funOf f arg) (funOf g arg) :=
    (singletonE_mem _ _).mp hval
  have hgoal : funOf (funOf (funOf s f) g) arg =
      funOf (funOf (funOf s f') g') arg := by
    rw [hsg, hsg']
  rw [hgoal, hval', Scomb_app3]

end DomainTheory.DataTypesAsLattices
