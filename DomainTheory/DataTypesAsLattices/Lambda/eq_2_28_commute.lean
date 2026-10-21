/-ai
Scott 1976, (2.28). The least fixed point of λf λx. g(x)(f(x)) is λx. Y(g(x)).

The functional is Scott continuous because it is the graph of a map continuous in x. It fixes the graph of x ↦ Y(g(x)), since each section satisfies its fixed-point equation, so the least fixed point lies below that graph. Applied to any argument, the iterates of the functional from ⊥ are the iterates of the corresponding section. A pair code in the graph of those least fixed points therefore lies in some positive iterate of the functional.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Ymap_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.28).** `Y(λf λx. g(x)(f(x))) = λx. Y(g(x))`. -/
theorem eq_2_28_commute {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    fix (Fofg g) = Ymap g := by
  have hF : IsScottContinuous (Fofg g) :=
    graph_const_isScottContinuous (fun f x => g x (funOf f x))
      (fun x => theorem_1_3 (hgy x) (funOf_isScottContinuous_left x))
  have hfix : Fofg g (Ymap g) = Ymap g := by
    apply congrArg graph
    funext x
    rw [Ymap_app hgx hgy]
    exact (theorem_1_4 (hgy x)).1
  have hle : fix (Fofg g) ⊆ Ymap g := (theorem_1_4 hF).2 (Ymap g) hfix
  refine subset_antisymm hle ?_
  have hiter : ∀ n x, funOf (iterateBot (Fofg g) n) x = iterateBot (g x) n := by
    intro n
    induction n with
    | zero =>
      intro x
      ext m
      simp [iterateBot, funOf, botElem]
    | succ n ih =>
      intro x
      have hcont : IsScottContinuous
          (fun z => g z (funOf (iterateBot (Fofg g) n) z)) :=
        theorem_1_3_tuple hgx hgy id_isScottContinuous
          (funOf_isScottContinuous (iterateBot (Fofg g) n))
      change funOf (lam (fun z => g z (funOf (iterateBot (Fofg g) n) z))) x =
        g x (iterateBot (g x) n)
      rw [beta hcont, ih]
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  obtain ⟨k, hkm⟩ := Set.mem_iUnion.mp hm
  cases k with
  | zero =>
    simp [iterateBot, botElem] at hkm
  | succ k =>
    have : pair n m ∈ iterateBot (Fofg g) (k + 1) :=
      ⟨n, m, rfl, by
        change m ∈ g (e n) (funOf (iterateBot (Fofg g) k) (e n))
        rw [hiter]
        exact hkm⟩
    exact Set.mem_iUnion.mpr ⟨k + 1, this⟩

end DomainTheory.DataTypesAsLattices
