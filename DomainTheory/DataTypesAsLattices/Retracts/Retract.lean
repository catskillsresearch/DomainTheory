module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Graph.beta
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Functional composition (Scott (4.5)): `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

namespace comp

theorem app (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf.isScottContinuous u) (funOf.isScottContinuous v)) x

theorem isScottContinuous_right (u : Pomega) :
    IsScottContinuous (fun v => comp u v) :=
  graph_const_isScottContinuous (fun v x => funOf u (funOf v x))
    (fun x => theorem_1_3 (funOf.isScottContinuous u) (funOf.isScottContinuous_left x))

theorem right_const (a : Pomega) :
    IsScottContinuous (fun u => comp u a) :=
  graph_const_isScottContinuous (fun u x => funOf u (funOf a x))
    (fun x => funOf.isScottContinuous_left (funOf a x))

end comp

/-- An element `a` is a retract iff `a = a ∘ a`. -/
class Retract (a : Pomega) : Prop where
  out : a = comp a a

/-- Scott’s `fun` of (4.1). -/
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

namespace funRetract

theorem app (u : Pomega) :
    funOf funRetract u = graph (fun x => funOf u x) :=
  beta (graph_const_isScottContinuous (fun u x => funOf u x)
    (fun x => funOf.isScottContinuous_left x)) u

theorem isRetract : Retract funRetract := by
  constructor
  apply graph_ext
  intro u
  rw [funRetract.app, funRetract.app]
  apply graph_ext
  intro x
  exact (beta (funOf.isScottContinuous u) x).symm

end funRetract

/-- Scott’s `bool` of (4.3). -/
def boolR : Pomega :=
  graph (fun u => dcondSet u (ofNat 0) (ofNat 1))

namespace boolR

theorem app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet.isScottContinuous_left (ofNat 0) (ofNat 1)) u

theorem isRetract : Retract boolR := by
  constructor
  apply graph_ext
  intro u
  rw [app, app, dcondSet.bool_idem]

end boolR

end DomainTheory.DataTypesAsLattices
