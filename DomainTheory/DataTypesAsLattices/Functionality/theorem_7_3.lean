module

public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Functionality.mem
public import DomainTheory.DataTypesAsLattices.Functionality.arrowE
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.emptyE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE_mem
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.Icomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app3
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app2_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.eta2_app
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_7_3.I_unique (i : Pomega)
    (hi : ∀ A, (arrowE A A).mem i) : i = Icomb := by
  have hgraph : i = graph (fun x => funOf i x) := (hi emptyE).1
  apply graph_funOf_ext hgraph Icomb_isGraph
  intro a
  have ha : (singletonE a).mem (funOf i a) :=
    (theorem_7_1 (singletonE a) (singletonE a)).2.1 (hi (singletonE a))
      ((singletonE_mem a a).mpr rfl)
  simpa [Icomb.app, singletonE_mem] using ha

theorem theorem_7_3.K_unique (k : Pomega)
    (hk : ∀ A B, (arrowE A (arrowE B A)).mem k) : k = Kcomb := by
  have hgraph : k = graph (fun x => funOf k x) := (hk emptyE emptyE).1
  apply graph_funOf_ext hgraph Kcomb_isGraph
  intro a
  have hkA : (arrowE (singletonE a) (arrowE emptyE (singletonE a))).mem k :=
    hk (singletonE a) emptyE
  have hka : (arrowE emptyE (singletonE a)).mem (funOf k a) :=
    (theorem_7_1 (singletonE a) (arrowE emptyE (singletonE a))).2.1 hkA
      ((singletonE_mem a a).mpr rfl)
  apply graph_funOf_ext hka.1 (Kcomb_app_isGraph a)
  intro b
  have hkAB : (arrowE (singletonE a) (arrowE (singletonE b) (singletonE a))).mem k :=
    hk (singletonE a) (singletonE b)
  have hkab : (arrowE (singletonE b) (singletonE a)).mem (funOf k a) :=
    (theorem_7_1 (singletonE a) (arrowE (singletonE b) (singletonE a))).2.1 hkAB
      ((singletonE_mem a a).mpr rfl)
  have hab : (singletonE a).mem (funOf (funOf k a) b) :=
    (theorem_7_1 (singletonE b) (singletonE a)).2.1 hkab
      ((singletonE_mem b b).mpr rfl)
  simpa [Kcomb_app2, singletonE_mem] using hab

theorem theorem_7_3.S_unique (s : Pomega)
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
    beta (funOf.isScottContinuous g) z
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
      exact (beta (funOf.isScottContinuous (funOf f z)) y).symm
    rw [hx₁, hx₂]
    refine ⟨hfxgraph arg, hfxgraph arg, ?_⟩
    intro y₁ y₂ hy
    have hy₁ : y₁ = funOf g arg := hy.1
    have hy₂ : y₂ = funOf g arg := hy.2
    rw [hy₁, hy₂, hf'app]
    have happ :
        funOf (graph (fun y => funOf (funOf f arg) y)) (funOf g arg) =
          funOf (funOf f arg) (funOf g arg) :=
      beta (funOf.isScottContinuous (funOf f arg)) (funOf g arg)
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

theorem theorem_7_3.i (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb :=
  ⟨Icomb_isGraph, Icomb_isGraph, fun x y hxy => by simpa [Icomb.app] using hxy⟩

theorem theorem_7_3.ii (A B : RestrictedEquiv) :
    (arrowE A (arrowE B A)).mem Kcomb := by
  refine ⟨Kcomb_isGraph, Kcomb_isGraph, ?_⟩
  intro x x' hx
  refine ⟨Kcomb_app_isGraph x, Kcomb_app_isGraph x', ?_⟩
  intro y y' _hy
  simpa [Kcomb_app2] using hx

theorem theorem_7_3.iii (A B C : RestrictedEquiv) :
    (arrowE (arrowE A (arrowE B C))
      (arrowE (arrowE A B) (arrowE A C))).mem Scomb := by
  refine ⟨Scomb_isGraph, Scomb_isGraph, ?_⟩
  intro f f' hf
  refine ⟨Scomb_app_isGraph f, Scomb_app_isGraph f', ?_⟩
  intro g g' hg
  refine ⟨Scomb_app2_isGraph f g, Scomb_app2_isGraph f' g', ?_⟩
  intro x x' hx
  have hgx : (arrowE A B).rel g g' := hg
  have hfx : (arrowE A (arrowE B C)).rel f f' := hf
  have hB : B.rel (funOf g x) (funOf g' x') := hgx.2.2 x x' hx
  have hBC : (arrowE B C).rel (funOf f x) (funOf f' x') := hfx.2.2 x x' hx
  simpa [Scomb_app3] using hBC.2.2 (funOf g x) (funOf g' x') hB

theorem theorem_7_3 :
    (∀ A, (arrowE A A).mem Icomb) ∧
      (∀ A B, (arrowE A (arrowE B A)).mem Kcomb) ∧
      (∀ A B C,
        (arrowE (arrowE A (arrowE B C))
          (arrowE (arrowE A B) (arrowE A C))).mem Scomb) ∧
      (∀ i, (∀ A, (arrowE A A).mem i) → i = Icomb) ∧
      (∀ k, (∀ A B, (arrowE A (arrowE B A)).mem k) → k = Kcomb) ∧
      (∀ s,
        (∀ f, funOf s f =
          funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y)))) →
        (∀ f g, funOf (funOf s f) g =
          funOf (funOf s f) (graph (fun x => funOf g x))) →
        (∀ A B C,
          (arrowE (arrowE A (arrowE B C))
            (arrowE (arrowE A B) (arrowE A C))).mem s) →
        s = Scomb) :=
  ⟨theorem_7_3.i, theorem_7_3.ii, theorem_7_3.iii,
    theorem_7_3.I_unique, theorem_7_3.K_unique, theorem_7_3.S_unique⟩

end DomainTheory.DataTypesAsLattices
