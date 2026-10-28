module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_11 (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by
  rw [arrowR.app, arrowR.app]

namespace eq_4_11

theorem comp (a b a' b' : Pomega) :
    DomainTheory.DataTypesAsLattices.comp (arrowR a b) (arrowR a' b') =
      arrowR (DomainTheory.DataTypesAsLattices.comp a' a)
        (DomainTheory.DataTypesAsLattices.comp b b') := by
  apply graph_ext
  intro u
  calc
    funOf (arrowR a b) (funOf (arrowR a' b') u)
        = DomainTheory.DataTypesAsLattices.comp b
            (DomainTheory.DataTypesAsLattices.comp (funOf (arrowR a' b') u) a) :=
          arrowR.app _ _ _
    _ = DomainTheory.DataTypesAsLattices.comp b
            (DomainTheory.DataTypesAsLattices.comp
              (DomainTheory.DataTypesAsLattices.comp b'
                (DomainTheory.DataTypesAsLattices.comp u a')) a) := by
          rw [arrowR.app]
    _ = DomainTheory.DataTypesAsLattices.comp
            (DomainTheory.DataTypesAsLattices.comp b b')
            (DomainTheory.DataTypesAsLattices.comp u
              (DomainTheory.DataTypesAsLattices.comp a' a)) := by
          apply graph_ext
          intro x
          simp only [DomainTheory.DataTypesAsLattices.comp.app]

end eq_4_11

end DomainTheory.DataTypesAsLattices
