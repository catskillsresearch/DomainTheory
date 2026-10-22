module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous
public import DomainTheory.ContinuousLattice.Constructions.scottExtend_maximal

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]


/-- **Scott 1972, Proposition 3.8.** If `E` is a continuous lattice and `e : X → Y` a subspace
embedding, then for each continuous `f : X → E` the explicit formula `scottExtend e f` is the
*maximal extension* of `f` to `[Y → E]`: it is Scott-continuous (`scottExtend_continuous`), it
restricts to `f` along `e` (`scottExtend_eq_of_continuous`), and it dominates every continuous
solution of `f' ∘ e = f` (`scottExtend_maximal`). -/
theorem proposition_3_8 (hE : ContinuousLattice E) (e : X → Y) (he : IsEmbedding e)
    (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f)
      ∧ (∀ x, scottExtend e f (e x) = f x)
      ∧ (∀ f' : Y → E, @Continuous Y E _ scottTopologicalSpace f' → (∀ x, f' (e x) = f x) →
          ∀ y, f' y ≤ scottExtend e f y) :=
  ⟨scottExtend_continuous hE e f,
   fun x => scottExtend_eq_of_continuous hE e he f hf x,
   fun _f' hf' h_ext y => scottExtend_maximal hE e hf' h_ext y⟩

end InjectiveExtension
end DomainTheory.ContinuousLattice
