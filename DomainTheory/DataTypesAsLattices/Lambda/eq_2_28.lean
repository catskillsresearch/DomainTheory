module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.Ymap
public import DomainTheory.DataTypesAsLattices.Lambda.Fofg
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_2_28 {g : Pomega → Pomega → Pomega}
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    fix (g x) = g x (fix (g x)) :=
  (theorem_1_4 (hgy x)).1.symm

namespace eq_2_28

theorem commute {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    fix (Fofg g) = Ymap g := by
  have hF : IsScottContinuous (Fofg g) :=
    graph_const_isScottContinuous (fun f x => g x (funOf f x))
      (fun x => theorem_1_3 (hgy x) (funOf.isScottContinuous_left x))
  have hfix : Fofg g (Ymap g) = Ymap g := by
    apply congrArg graph
    funext x
    rw [Ymap.app hgx hgy]
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
        theorem_1_3.tuple hgx hgy id_isScottContinuous
          (funOf.isScottContinuous (iterateBot (Fofg g) n))
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

end eq_2_28

end DomainTheory.DataTypesAsLattices
