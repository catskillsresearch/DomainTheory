module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE_mem
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app2
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_isGraph
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem theorem_7_3_K_unique (k : Pomega)
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

end DomainTheory.DataTypesAsLattices
