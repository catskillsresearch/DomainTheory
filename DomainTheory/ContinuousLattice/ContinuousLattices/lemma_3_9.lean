module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection
public import DomainTheory.ContinuousLattice.Constructions.scottExtend
import DomainTheory.ContinuousLattice.Constructions.scottExtend_continuous
import DomainTheory.ContinuousLattice.Constructions.scottExtend_eq_of_continuous
import DomainTheory.ContinuousLattice.Constructions.scottExtend_maximal
import DomainTheory.ContinuousLattice.Constructions.scottExtend_maximal_le

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section Lemma39

variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']

theorem lemma_3_9 (hD : ContinuousLattice D) (hD' : ContinuousLattice D')
    (P : ContinuousLatticeProjection D D') (e : X → Y) (he : IsEmbedding e)
    {f : X → D} {g : X → D'} (hf : @Continuous X D _ scottTopologicalSpace f)
    (hg : @Continuous X D' _ scottTopologicalSpace g)
    (hfg : ∀ x, f x = (P.retr : D' → D) (g x)) (y : Y) :
    scottExtend e f y = (P.retr : D' → D) (scottExtend e g y) := by
  have hfbar : @Continuous Y D _ scottTopologicalSpace (scottExtend e f) :=
    scottExtend_continuous hD e f
  have hgbar : @Continuous Y D' _ scottTopologicalSpace (scottExtend e g) :=
    scottExtend_continuous hD' e g

  have hjg : @Continuous Y D _ scottTopologicalSpace (fun z => (P.retr : D' → D) (scottExtend e g z)) := by
    let : TopologicalSpace D := scottTopologicalSpace
    let : TopologicalSpace D' := scottTopologicalSpace
    exact P.retr.continuous.comp hgbar
  have hif : @Continuous Y D' _ scottTopologicalSpace (fun z => (P.incl : D → D') (scottExtend e f z)) := by
    let : TopologicalSpace D := scottTopologicalSpace
    let : TopologicalSpace D' := scottTopologicalSpace
    exact P.incl.continuous.comp hfbar

  have hA : ∀ z, (P.retr : D' → D) (scottExtend e g z) ≤ scottExtend e f z := by
    intro z
    refine scottExtend_maximal hD e hjg ?_ z
    intro x
    show (P.retr : D' → D) (scottExtend e g (e x)) = f x
    rw [scottExtend_eq_of_continuous hD' e he g hg x, ← hfg x]

  have hB : ∀ z, (P.incl : D → D') (scottExtend e f z) ≤ scottExtend e g z := by
    intro z
    refine scottExtend_maximal_le hD' e hif ?_ z
    intro x
    show (P.incl : D → D') (scottExtend e f (e x)) ≤ g x
    rw [scottExtend_eq_of_continuous hD e he f hf x, hfg x]
    exact P.incl_retr_le (g x)
  refine le_antisymm ?_ (hA y)
  calc scottExtend e f y
      = (P.retr : D' → D) ((P.incl : D → D') (scottExtend e f y)) :=
        (P.retr_incl (scottExtend e f y)).symm
    _ ≤ (P.retr : D' → D) (scottExtend e g y) := P.retr.monotone (hB y)

end Lemma39
end DomainTheory.ContinuousLattice
